module Main

import Data.Either
import Data.List
import Data.String
import Data.Vect
import Hedgehog
import System
import System.Directory
import System.File
import Text.YAML

%default total

--------------------------------------------------------------------------------
--          YAML Test Suite Runner
--------------------------------------------------------------------------------

-- Parses a string to YAML events. Stub until `Text.YAML.Parser` lands.
parseStr : String -> Either String (List Event)
parseStr _ = Left "YAML parser not yet implemented"

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
    bases = map (++ "suite") ["", "test/", "yaml/test/"]

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
  id  : String
  ok  : Bool
  msg : String

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
    | Left err => pure (CR id False "cannot read in.yaml: \{show err}")
  isErr <- isFile "\{dir}/error"
  case parseStr inp of
    Left err => case isErr of
      True  => pure (CR id True "")
      False => pure (CR id False "parse error: \{err}")
    Right evs => case isErr of
      True  => pure (CR id False "expected a parse error")
      False => do
        Right expected <- readFile "\{dir}/test.event"
          | Left err => pure (CR id False "cannot read test.event: \{show err}")
        case firstDiff (lines expected) (map printEvent evs) of
          Nothing => pure (CR id True "")
          Just d  => pure (CR id False d)

covering
knownFailures : (path : String) -> IO (List String)
knownFailures path = do
  Right s <- readFile path | Left _ => pure []
  pure . filter (/= "") $ lines s

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
  putStrLn "yaml-test-suite: \{show $ length rs `minus` length failed}/\{show $ length rs} passed (\{show $ length exp} known failures)"
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

properties : Group
properties =
  MkGroup
    "Text.YAML"
    [ ("prop_printedEventIsSingleLine", prop_printedEventIsSingleLine)
    ]

covering
main : IO ()
main = do
  True <- runSuite | False => exitFailure
  test [ properties ]
