module Main

import Data.Either
import Data.List
import Data.String
import Data.Vect
import Hedgehog
import JSON.Parser
import System
import System.Directory
import System.File
import Text.YAML

%default total

--------------------------------------------------------------------------------
--          YAML Test Suite Runner
--------------------------------------------------------------------------------

parseStr : String -> Either String (List Event)
parseStr = mapFst interpolate . parseEvents Virtual

--------------------------------------------------------------------------------
--          Comparing Composed Documents Against in.json
--------------------------------------------------------------------------------

-- Converts a composed node to its JSON interpretation: scalars by
-- their resolved tag (falling back to the raw text where a tag lies
-- about its content, so mismatches surface as diffs), collections by
-- shape, mapping keys by their raw scalar text. Fails only on
-- non-scalar mapping keys, which JSON cannot represent.
mutual
  toJSON : Node -> Maybe JSON
  toJSON n@(NScalar t _ s) = Just $ case t of
    TNull  => JNull
    TBool  => maybe (JString s) JBool (asBool n)
    TInt   => maybe (JString s) JInteger (asInteger n)
    TFloat => maybe (JString s) JDouble (asDouble n)
    _      => JString s
  toJSON (NSeq _ ns) = JArray <$> toJSONs [<] ns
  toJSON (NMap _ ps) = JObject <$> toPairs [<] ps

  toJSONs : SnocList JSON -> List Node -> Maybe (List JSON)
  toJSONs acc []        = Just (acc <>> [])
  toJSONs acc (n :: ns) = case toJSON n of
    Just j  => toJSONs (acc :< j) ns
    Nothing => Nothing

  toPairs : SnocList (String, JSON) -> List (Node, Node) -> Maybe (List (String, JSON))
  toPairs acc []                         = Just (acc <>> [])
  toPairs acc ((NScalar _ _ k, v) :: ps) = case toJSON v of
    Just jv => toPairs (acc :< (k, jv)) ps
    Nothing => Nothing
  toPairs acc _                          = Nothing

||| The suite's in.json files hold one JSON value per document,
||| concatenated. `parseJSON` rejects trailing content, so accumulating
||| lines until a prefix parses splits them reliably.
jsonDocs : String -> Maybe (List JSON)
jsonDocs s = go [<] [<] (lines s)

  where
    go : SnocList JSON -> SnocList String -> List String -> Maybe (List JSON)
    go js pend [] =
      if all (\l => trim l == "") (pend <>> [])
        then Just (js <>> [])
        else Nothing
    go js pend (l :: ls) =
      let pend2 := pend :< l
       in case parseJSON Virtual (unlines (pend2 <>> [])) of
            Right j => go (js :< j) [<] ls
            Left _  => go js pend2 ls

-- JSON equivalence as the suite intends it: object member order is
-- insignificant (in.json does not preserve the mapping's order), and
-- numbers compare by value (the suite renders the YAML float `450.00`
-- as the JSON integer `450`).
mutual
  jeq : JSON -> JSON -> Bool
  jeq (JInteger a) (JDouble b)  = cast a == b
  jeq (JDouble a)  (JInteger b) = a == cast b
  jeq (JArray as)  (JArray bs)  = jeqs as bs
  jeq (JObject as) (JObject bs) = length as == length bs && jeqPairs as bs
  jeq a            b            = a == b

  jeqs : List JSON -> List JSON -> Bool
  jeqs []        []        = True
  jeqs (a :: as) (b :: bs) = jeq a b && jeqs as bs
  jeqs _         _         = False

  jeqPairs : List (String, JSON) -> List (String, JSON) -> Bool
  jeqPairs []             _  = True
  jeqPairs ((k, v) :: as) bs = case lookup k bs of
    Just v2 => jeq v v2 && jeqPairs as bs
    Nothing => False

jsonDiff : (expected, got : List JSON) -> Maybe String
jsonDiff []        []        = Nothing
jsonDiff (e :: _)  []        = Just "missing document, expected: \{show e}"
jsonDiff []        (g :: _)  = Just "extra document: \{show g}"
jsonDiff (e :: es) (g :: gs) =
  if jeq e g
    then jsonDiff es gs
    else Just "expected json: \{show e}\n          got: \{show g}"

-- Whether and how a case's in.json comparison was performed.
data JState = NoJson | Compared | JSkipped

-- Composes the events and compares the documents' JSON interpretation
-- against the case's in.json content.
checkJSON : (events : List Event) -> (inJson : String) -> (JState, Maybe String)
checkJSON evs js = case jsonDocs js of
  Nothing  => (Compared, Just "cannot split in.json into documents")
  Just exp => case compose evs of
    Left e     => (Compared, Just "compose error: \{e}")
    Right docs => case toJSONs [<] docs of
      Nothing  => (JSkipped, Nothing)
      Just got => (Compared, jsonDiff exp got)

-- Directory containing the vendored test suite data plus the path
-- of the known-failures ratchet file.
record Paths where
  constructor MkPaths
  suite : String
  known : String

covering
isDir : String -> IO Bool
isDir = map isRight . listDir

covering
isFile : String -> IO Bool
isFile = map isRight . readFile

||| `pack test` may invoke the runner from different working directories,
||| so we probe the known locations of the suite data.
covering
findPaths : IO (Maybe Paths)
findPaths = do
  env <- getEnv "YAML_TEST_SUITE_DIR"
  go (maybe bases (:: bases) env)

  where
    bases : List String
    bases = map (++ "suite") ["", "test/"]

    go : List String -> IO (Maybe Paths)
    go []        = pure Nothing
    go (b :: bs) = do
      True <- isDir b | False => go bs
      pure $ Just (MkPaths b (b ++ "/../known-failures.txt"))

||| Lists the IDs of all test cases: directories containing an `in.yaml`,
||| either directly (`229Q`) or in numbered subdirectories (`VJP3/00`).
covering
caseIds : (suite : String) -> IO (List String)
caseIds suite = do
  Right es <- listDir suite | Left err => pure []
  map (sort . concat) $ traverse topCase (sort es)

  where
    subCase : (top : String) -> (sub : String) -> IO (List String)
    subCase top sub = do
      let id := top ++ "/" ++ sub
      True <- isFile "\{suite}/\{id}/in.yaml" | False => pure []
      pure [id]

    topCase : String -> IO (List String)
    topCase e = do
      True <- isFile "\{suite}/\{e}/in.yaml"
        | False => do
            Right subs <- listDir "\{suite}/\{e}" | Left _ => pure []
            map concat $ traverse (subCase e) subs
      pure [e]

record CaseResult where
  constructor CR
  id   : String
  ok   : Bool
  json : JState
  msg  : String

firstDiff : (expected, got : List String) -> Maybe String
firstDiff []        []        = Nothing
firstDiff (e :: _)  []        = Just "missing event, expected: \{e}"
firstDiff []        (g :: _)  = Just "extra event: \{g}"
firstDiff (e :: es) (g :: gs) =
  if e == g
    then firstDiff es gs
    else Just "expected: \{e}\n        got: \{g}"

covering
runCase : (suite : String) -> (id : String) -> IO CaseResult
runCase suite id = do
  let dir := "\{suite}/\{id}"
  Right inp <- readFile "\{dir}/in.yaml"
    | Left err => pure (CR id False NoJson "cannot read in.yaml: \{show err}")
  isErr <- isFile "\{dir}/error"
  case parseStr inp of
    Left err => case isErr of
      True  => pure (CR id True NoJson "")
      False => pure (CR id False NoJson "parse error: \{err}")
    Right evs => case isErr of
      True  => pure (CR id False NoJson "expected a parse error")
      False => do
        Right expected <- readFile "\{dir}/test.event"
          | Left err => pure (CR id False NoJson "cannot read test.event: \{show err}")
        case firstDiff (lines expected) (map printEvent evs) of
          Just d  => pure (CR id False NoJson d)
          Nothing => do
            -- events match; check the composed documents where the
            -- suite provides their JSON interpretation
            Right js <- readFile "\{dir}/in.json"
              | Left _ => pure (CR id True NoJson "")
            case checkJSON evs js of
              (st, Nothing) => pure (CR id True st "")
              (st, Just d)  => pure (CR id False st d)

covering
knownFailures : (path : String) -> IO (List String)
knownFailures path = do
  Right s <- readFile path | Left _ => pure []
  pure . filter (\l => l /= "" && not ("#" `isPrefixOf` l)) $ lines s

||| Runs the whole suite, comparing the outcome against the
||| known-failures ratchet: the run is good iff no case outside
||| `known-failures.txt` fails and no case inside it passes.
covering
runSuite : IO Bool
runSuite = do
  Just (MkPaths suite known) <- findPaths
    | Nothing => putStrLn "could not locate the test suite data" $> False
  ids@(_ :: _) <- caseIds suite
    | [] => putStrLn "no test cases found in \{suite}" $> False
  rs    <- traverse (runCase suite) ids
  exp   <- knownFailures known
  let failed   := filter (not . ok) rs
      newFails := filter (\r => not $ r.id `elem` exp) failed
      passedId := map (.id) $ filter ok rs
      newPass  := filter (`elem` passedId) exp
      stale    := filter (\i => not $ i `elem` map (.id) rs) exp
  let nCmp  := length $ filter (\r => case r.json of Compared => True; _ => False) rs
      nSkip := length $ filter (\r => case r.json of JSkipped => True; _ => False) rs
  putStrLn "yaml-test-suite: \{show $ length rs `minus` length failed}/\{show $ length rs} passed (\{show $ length exp} known failures, json: \{show nCmp} compared, \{show nSkip} skipped)"
  traverse_ (\r => putStrLn "\nunexpected failure: \{r.id}\n  \{r.msg}") newFails
  traverse_ (\i => putStrLn "\nnow passing (remove from known-failures.txt): \{i}") newPass
  traverse_ (\i => putStrLn "\nstale entry in known-failures.txt: \{i}") stale
  pure $ null newFails && null newPass && null stale

--------------------------------------------------------------------------------
--          Properties
--------------------------------------------------------------------------------

genAnchor : Gen (Maybe Anchor)
genAnchor = maybe (string (linear 1 5) alphaNum)

genTag : Gen Types.Tag
genTag =
  choice
    [ pure NoTag
    , pure NonSpec
    , Verbatim . ("tag:" ++) <$> string (linear 1 10) alphaNum
    ]

genStyle : Gen Style
genStyle = element [Plain, SingleQ, DoubleQ, Literal, Folded]

genEvent : Gen Event
genEvent =
  frequency
    [ (1, element [StreamStart, StreamEnd, SeqEnd, MapEnd])
    , (1, DocStart <$> bool)
    , (1, DocEnd <$> bool)
    , (2, [| SeqStart bool genAnchor genTag |])
    , (2, [| MapStart bool genAnchor genTag |])
    , (2, Alias <$> string (linear 1 5) alphaNum)
    , (5, [| Scalar genAnchor genTag genStyle (string (linear 0 20) unicode) |])
    ]

-- `printEvent` must always produce a single line: line breaks and
-- other special characters in scalar values are escaped.
prop_printedEventIsSingleLine : Property
prop_printedEventIsSingleLine = property $ do
  e <- forAll genEvent
  assert $ all (\c => not $ c `elem` the (List Char) ['\n','\r','\t','\b','\0'])
               (unpack $ printEvent e)

data Lvl = LStr | LDoc | LSeq | LMap

-- Are the events well nested: a single stream of documents, each
-- holding one node tree, with all collections closed in order?
balanced : List Event -> Bool
balanced = go []

  where
    inNode : List Lvl -> Bool
    inNode (LDoc :: _) = True
    inNode (LSeq :: _) = True
    inNode (LMap :: _) = True
    inNode _           = False

    go : List Lvl -> List Event -> Bool
    go []            (StreamStart :: es)    = go [LStr] es
    go [LStr]        (StreamEnd :: es)      = null es
    go st@[LStr]     (DocStart _ :: es)     = go (LDoc :: st) es
    go (LDoc :: st)  (DocEnd _ :: es)       = go st es
    go st            (SeqStart _ _ _ :: es) = inNode st && go (LSeq :: st) es
    go (LSeq :: st)  (SeqEnd :: es)         = go st es
    go st            (MapStart _ _ _ :: es) = inNode st && go (LMap :: st) es
    go (LMap :: st)  (MapEnd :: es)         = go st es
    go st            (Scalar _ _ _ _ :: es) = inNode st && go st es
    go st            (Alias _ :: es)        = inNode st && go st es
    go _             _                      = False

yamlChar : Gen Char
yamlChar =
  frequency
    [ (10, printableAscii)
    , (8, element [' ', '\n', ':', '-', '#', '[', ']', '{', '}', ',', '?', '&', '*', '!', '"', '\'', '|', '>'])
    , (1, unicode)
    ]

-- Whatever the input, a successful parse yields well nested events.
prop_parsedEventsBalanced : Property
prop_parsedEventsBalanced = property $ do
  s <- forAll (string (linear 0 60) yamlChar)
  case parseEvents Virtual s of
    Left _    => assert True
    Right evs => assert (balanced evs)

properties : Group
properties =
  MkGroup
    "Text.YAML"
    [ ("prop_printedEventIsSingleLine", prop_printedEventIsSingleLine)
    , ("prop_parsedEventsBalanced", prop_parsedEventsBalanced)
    ]

--------------------------------------------------------------------------------
--          Composer Properties
--------------------------------------------------------------------------------

-- rendered integers resolve as ints and read back
prop_intsResolve : Property
prop_intsResolve = property $ do
  n <- forAll (integer $ exponentialFrom 0 (-0x10000000000000000) 0x10000000000000000)
  resolvePlain (show n) === TInt
  asInteger (NScalar TInt Plain (show n)) === Just n

-- non-plain scalars never resolve to a non-string tag
prop_quotedIsStr : Property
prop_quotedIsStr = property $ do
  s   <- forAll (string (linear 0 10) unicode)
  sty <- forAll (element [SingleQ, DoubleQ, Literal, Folded])
  scalarTag Core NoTag sty s === TStr

-- alphabetic plain scalars outside the special word lists are strings
-- (an `x` prefix keeps the generated words out of those lists)
prop_alphaIsStr : Property
prop_alphaIsStr = property $ do
  s <- forAll (string (linear 0 9) alpha)
  resolvePlain ("x" ++ s) === TStr

-- decimal fractions resolve as floats and read back
prop_floatsResolve : Property
prop_floatsResolve = property $ do
  ip <- forAll (string (linear 1 6) digit)
  fp <- forAll (string (linear 1 6) digit)
  let s := "\{ip}.\{fp}"
  resolvePlain s === TFloat
  assert $ isJust (asDouble (NScalar TFloat Plain s))

scalar : STag -> String -> Node
scalar t = NScalar t Plain

-- behavioral unit cases, parsed end to end via parseDocs
prop_aliasSharing : Property
prop_aliasSharing = withTests 1 $ property $
  parseDocs Virtual "[&a x, *a]" ===
    Right [NSeq TSeq [scalar TStr "x", scalar TStr "x"]]

prop_cyclicAlias : Property
prop_cyclicAlias = withTests 1 $ property $
  parseDocs Virtual "&a [*a]" === Left (YCompose (CyclicAlias "a"))

prop_undefinedAlias : Property
prop_undefinedAlias = withTests 1 $ property $
  parseDocs Virtual "[*nope]" === Left (YCompose (UndefinedAlias "nope"))

-- the plain key `a` and the quoted key "a" are equal: styles do not
-- distinguish keys
prop_dupKeyAcrossStyles : Property
prop_dupKeyAcrossStyles = withTests 1 $ property $
  parseDocs Virtual "{a: 1, \"a\": 2}" ===
    Left (YCompose (DuplicateKey (scalar TStr "a")))

prop_anchorShadowing : Property
prop_anchorShadowing = withTests 1 $ property $
  parseDocs Virtual "[&a 1, &a 2, *a]" ===
    Right [NSeq TSeq [scalar TInt "1", scalar TInt "2", scalar TInt "2"]]

prop_emptyDocIsNull : Property
prop_emptyDocIsNull = withTests 1 $ property $
  parseDocs Virtual "---" === Right [scalar TNull ""]

composeProps : Group
composeProps =
  MkGroup
    "Text.YAML.Compose"
    [ ("prop_intsResolve", prop_intsResolve)
    , ("prop_quotedIsStr", prop_quotedIsStr)
    , ("prop_alphaIsStr", prop_alphaIsStr)
    , ("prop_floatsResolve", prop_floatsResolve)
    , ("prop_aliasSharing", prop_aliasSharing)
    , ("prop_cyclicAlias", prop_cyclicAlias)
    , ("prop_undefinedAlias", prop_undefinedAlias)
    , ("prop_dupKeyAcrossStyles", prop_dupKeyAcrossStyles)
    , ("prop_anchorShadowing", prop_anchorShadowing)
    , ("prop_emptyDocIsNull", prop_emptyDocIsNull)
    ]

covering
main : IO ()
main = do
  True <- runSuite | False => exitFailure
  test [ properties, composeProps ]
