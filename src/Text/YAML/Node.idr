module Text.YAML.Node

import Data.String
import Derive.Prelude
import Text.YAML.Types

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Specific Tags
--------------------------------------------------------------------------------

||| A node's specific tag after schema resolution [spec chapter 10].
|||
||| The tags of the core schema get their own constructors for cheap
||| matching; anything else (`tag:yaml.org,2002:set`, local `!foo`
||| tags, ...) is `TOther`.
public export
data STag : Type where
  TNull  : STag
  TBool  : STag
  TInt   : STag
  TFloat : STag
  TStr   : STag
  TSeq   : STag
  TMap   : STag
  TOther : String -> STag

%runElab derive "STag" [Show,Eq]

||| The URI form of a specific tag, e.g. `tag:yaml.org,2002:int`.
public export
tagURI : STag -> String
tagURI TNull      = "tag:yaml.org,2002:null"
tagURI TBool      = "tag:yaml.org,2002:bool"
tagURI TInt       = "tag:yaml.org,2002:int"
tagURI TFloat     = "tag:yaml.org,2002:float"
tagURI TStr       = "tag:yaml.org,2002:str"
tagURI TSeq       = "tag:yaml.org,2002:seq"
tagURI TMap       = "tag:yaml.org,2002:map"
tagURI (TOther s) = s

||| Inverse of `tagURI`: maps the core schema URIs to their
||| constructors, anything else to `TOther`.
public export
fromURI : String -> STag
fromURI "tag:yaml.org,2002:null"  = TNull
fromURI "tag:yaml.org,2002:bool"  = TBool
fromURI "tag:yaml.org,2002:int"   = TInt
fromURI "tag:yaml.org,2002:float" = TFloat
fromURI "tag:yaml.org,2002:str"   = TStr
fromURI "tag:yaml.org,2002:seq"   = TSeq
fromURI "tag:yaml.org,2002:map"   = TMap
fromURI s                         = TOther s

--------------------------------------------------------------------------------
--          Nodes
--------------------------------------------------------------------------------

||| A composed YAML node: the output of the composer, with aliases
||| substituted and tags resolved.
|||
||| Scalars keep their raw text (interpreted on demand by the views
||| below) together with their presentation style.
public export
data Node : Type where
  NScalar : (tag : STag) -> (style : Style) -> (text : String) -> Node
  NSeq    : (tag : STag) -> List Node -> Node
  NMap    : (tag : STag) -> List (Node, Node) -> Node

scText : SnocList String -> String -> SnocList String
scText ss s = ss :< show s

mutual
  showNode : SnocList String -> Node -> SnocList String
  showNode ss (NScalar _ _ s)       = scText ss s
  showNode ss (NSeq _ [])           = ss :< "[]"
  showNode ss (NSeq _ (n :: ns))    = showNodes (showNode (ss :< "[") n) ns
  showNode ss (NMap _ [])           = ss :< "{}"
  showNode ss (NMap _ (p :: ps))    = showPairs (showPair (ss :< "{") p) ps

  showPair : SnocList String -> (Node, Node) -> SnocList String
  showPair ss (k, v) = showNode (showNode ss k :< ": ") v

  showNodes : SnocList String -> List Node -> SnocList String
  showNodes ss []        = ss :< "]"
  showNodes ss (n :: ns) = showNodes (showNode (ss :< ", ") n) ns

  showPairs : SnocList String -> List (Node, Node) -> SnocList String
  showPairs ss []        = ss :< "}"
  showPairs ss (p :: ps) = showPairs (showPair (ss :< ", ") p) ps

||| Renders a node in compact flow style, with all scalars quoted.
export
canon : Node -> String
canon n = fastConcat (showNode [<] n <>> [])

export %inline
Show Node where
  show = canon

--------------------------------------------------------------------------------
--          Schemas and Scalar Resolution
--------------------------------------------------------------------------------

||| The schema used to resolve the tags of untagged nodes
||| [spec chapter 10].
public export
data Schema : Type where
  ||| Untagged scalars and collections become str/seq/map.
  Failsafe : Schema

  ||| Untagged plain scalars additionally resolve to null, bool, int
  ||| and float by their form. The recommended default.
  Core     : Schema

%runElab derive "Schema" [Show,Eq]

-- non-empty and all characters match
all1 : (Char -> Bool) -> List Char -> Bool
all1 f [] = False
all1 f cs = all f cs

-- [-+]?[0-9]+ | 0o[0-7]+ | 0x[0-9a-fA-F]+
isIntCs : List Char -> Bool
isIntCs ('0' :: 'x' :: cs) = all1 isHexDigit cs
isIntCs ('0' :: 'o' :: cs) = all1 isOctDigit cs
isIntCs ('+' :: cs)        = all1 isDigit cs
isIntCs ('-' :: cs)        = all1 isDigit cs
isIntCs cs                 = all1 isDigit cs

-- [eE][-+]?[0-9]+ or nothing
expPart : List Char -> Bool
expPart []                = True
expPart (e :: '+' :: cs)  = (e == 'e' || e == 'E') && all1 isDigit cs
expPart (e :: '-' :: cs)  = (e == 'e' || e == 'E') && all1 isDigit cs
expPart (e :: cs)         = (e == 'e' || e == 'E') && all1 isDigit cs

-- \.[0-9]+ | [0-9]+(\.[0-9]*)? , returning the rest for `expPart`
mantissa : List Char -> Maybe (List Char)
mantissa ('.' :: cs) = case span isDigit cs of
  ([], _) => Nothing
  (_, r)  => Just r
mantissa cs = case span isDigit cs of
  ([], _)        => Nothing
  (_, '.' :: r)  => Just (snd $ span isDigit r)
  (_, r)         => Just r

-- [-+]? mantissa expPart
isFloatCs : List Char -> Bool
isFloatCs ('+' :: cs) = maybe False expPart (mantissa cs)
isFloatCs ('-' :: cs) = maybe False expPart (mantissa cs)
isFloatCs cs          = maybe False expPart (mantissa cs)

nullWords, boolWords, infWords, nanWords : List String
trueWords, falseWords, posInfWords, negInfWords : List String
trueWords   = ["true", "True", "TRUE"]
falseWords  = ["false", "False", "FALSE"]
posInfWords = ["+.inf", ".inf", "+.Inf", ".Inf", "+.INF", ".INF"]
negInfWords = ["-.inf", "-.Inf", "-.INF"]
nullWords = ["", "~", "null", "Null", "NULL"]
boolWords = ["true", "True", "TRUE", "false", "False", "FALSE"]
infWords  =
  [ ".inf", "+.inf", "-.inf", ".Inf", "+.Inf", "-.Inf"
  , ".INF", "+.INF", "-.INF"
  ]
nanWords  = [".nan", ".NaN", ".NAN"]

||| The specific tag of an untagged plain scalar under the core schema
||| [spec 10.3.2].
export
resolvePlain : String -> STag
resolvePlain s =
  if s `elem` nullWords then TNull
  else if s `elem` boolWords then TBool
  else if (s `elem` infWords) || (s `elem` nanWords) then TFloat
  else
    let cs := unpack s
     in if isIntCs cs then TInt
        else if isFloatCs cs then TFloat
        else TStr

||| The specific tag of a scalar node. Explicitly tagged scalars keep
||| their tag without validation: a `!!int abc` node composes fine, and
||| the typed views below surface the mismatch on access.
export
scalarTag : Schema -> Tag -> Style -> String -> STag
scalarTag _    (Verbatim t) _     _ = fromURI t
scalarTag _    NonSpec      _     _ = TStr
scalarTag Core NoTag        Plain s = resolvePlain s
scalarTag _    NoTag        _     _ = TStr

||| The specific tag of a collection node, given its default
||| (`TSeq` or `TMap`).
export
collTag : Schema -> Tag -> (dflt : STag) -> STag
collTag _ (Verbatim t) _    = fromURI t
collTag _ _            dflt = dflt

--------------------------------------------------------------------------------
--          Typed Views
--------------------------------------------------------------------------------

public export %inline
nodeTag : Node -> STag
nodeTag (NScalar t _ _) = t
nodeTag (NSeq t _)      = t
nodeTag (NMap t _)      = t

public export %inline
isNull : Node -> Bool
isNull n = nodeTag n == TNull

||| The raw text of any scalar node.
public export
asText : Node -> Maybe String
asText (NScalar _ _ s) = Just s
asText _               = Nothing

||| The text of a str-tagged scalar node.
public export
asString : Node -> Maybe String
asString (NScalar TStr _ s) = Just s
asString _                  = Nothing

||| The value of a bool-tagged scalar node.
public export
asBool : Node -> Maybe Bool
asBool (NScalar TBool _ s) =
  if s `elem` trueWords then Just True
  else if s `elem` falseWords then Just False
  else Nothing
asBool _ = Nothing

digits : (base : Integer) -> (Char -> Maybe Integer) -> List Char -> Maybe Integer
digits base f [] = Nothing
digits base f cs = go 0 cs
  where
    go : Integer -> List Char -> Maybe Integer
    go acc []        = Just acc
    go acc (c :: t)  = case f c of
      Just d  => go (acc * base + d) t
      Nothing => Nothing

decDigit, octDigit', hexDigit' : Char -> Maybe Integer
decDigit c  = if isDigit c then Just (cast (ord c - 0x30)) else Nothing
octDigit' c = if isOctDigit c then Just (cast (ord c - 0x30)) else Nothing
hexDigit' c =
  if isDigit c then Just (cast (ord c - 0x30))
  else if c >= 'a' && c <= 'f' then Just (cast (ord c - 0x57))
  else if c >= 'A' && c <= 'F' then Just (cast (ord c - 0x37))
  else Nothing

intVal : List Char -> Maybe Integer
intVal ('0' :: 'x' :: cs) = digits 16 hexDigit' cs
intVal ('0' :: 'o' :: cs) = digits 8 octDigit' cs
intVal ('+' :: cs)        = digits 10 decDigit cs
intVal ('-' :: cs)        = negate <$> digits 10 decDigit cs
intVal cs                 = digits 10 decDigit cs

||| The value of an int-tagged scalar node (decimal with optional
||| sign, `0x` hexadecimal or `0o` octal).
public export
asInteger : Node -> Maybe Integer
asInteger (NScalar TInt _ s) = intVal (unpack s)
asInteger _                  = Nothing

-- Decomposes a core schema float (sign already stripped) into its
-- integer digits, fraction digits and exponent value: at least one
-- mantissa digit, an optional fraction and an optional exponent.
floatParts : List Char -> Maybe (List Char, List Char, Integer)
floatParts cs =
  let (ip, r1) := span isDigit cs
      (fp, r2) := case r1 of
                    '.' :: t => span isDigit t
                    _        => ([], r1)
   in case (ip, fp) of
        ([], []) => Nothing
        _        => (\e => (ip, fp, e)) <$> expVal r2

  where
    expVal : List Char -> Maybe Integer
    expVal []       = Just 0
    expVal (e :: r) =
      if e == 'e' || e == 'E'
        then case r of
          '+' :: ds => digits 10 decDigit ds
          '-' :: ds => negate <$> digits 10 decDigit ds
          ds        => digits 10 decDigit ds
        else Nothing

-- Rebuilds a float in a form every backend's `cast String Double`
-- handles (`.5`, `5.` and `1.e3` are valid YAML but not portable
-- strtod input).
dblVal : String -> Maybe Double
dblVal s =
  if s `elem` posInfWords
    then Just (1.0 / 0.0)
  else if s `elem` negInfWords
    then Just (-1.0 / 0.0)
  else if s `elem` nanWords
    then Just (0.0 / 0.0)
  else case unpack s of
    '+' :: cs => build "" cs
    '-' :: cs => build "-" cs
    cs        => build "" cs

  where
    orZero : List Char -> String
    orZero [] = "0"
    orZero cs = pack cs

    build : String -> List Char -> Maybe Double
    build sign cs =
      (\(ip, fp, e) => cast "\{sign}\{orZero ip}.\{orZero fp}e\{show e}")
        <$> floatParts cs

||| The numeric value of a float- or int-tagged scalar node.
public export
asDouble : Node -> Maybe Double
asDouble (NScalar TFloat _ s) = dblVal s
asDouble n@(NScalar TInt _ _) = cast <$> asInteger n
asDouble _                    = Nothing

public export
asSeq : Node -> Maybe (List Node)
asSeq (NSeq _ ns) = Just ns
asSeq _           = Nothing

public export
asMap : Node -> Maybe (List (Node, Node))
asMap (NMap _ ps) = Just ps
asMap _           = Nothing

||| The value of the first mapping entry whose key is a scalar with
||| the given raw text.
public export
lookupKey : String -> Node -> Maybe Node
lookupKey s (NMap _ ps) = go ps
  where
    go : List (Node, Node) -> Maybe Node
    go []                          = Nothing
    go ((NScalar _ _ t, v) :: rest) = if t == s then Just v else go rest
    go (_ :: rest)                  = go rest
lookupKey _ _ = Nothing

--------------------------------------------------------------------------------
--          Node Equality
--------------------------------------------------------------------------------

-- The canonical value of a core schema scalar [spec 10.3.2]. Floats
-- are kept in exact decimal scientific notation rather than as
-- `Double`: IEEE comparison would break reflexivity (NaN /= NaN) and
-- collapse out-of-range values (1e400 == 2e400 == +inf).
data CScalar : Type where
  CNull : CScalar
  CBool : Bool -> CScalar
  CInt  : Integer -> CScalar
  CZero : CScalar
  CInf  : (neg : Bool) -> CScalar
  CNaN  : CScalar
  -- value = (-1)^neg * d1.d2...dn * 10^exp, where `digits` are
  -- d1...dn with d1 and dn nonzero [spec: canonical float form]
  CSci  : (neg : Bool) -> (digits : String) -> (exp : Integer) -> CScalar

Eq CScalar where
  CNull       == CNull       = True
  CBool x     == CBool y     = x == y
  CInt x      == CInt y      = x == y
  CZero       == CZero       = True
  CInf x      == CInf y      = x == y
  CNaN        == CNaN        = True
  CSci n d e  == CSci m f g  = n == m && d == f && e == g
  _           == _           = False

canonFloat : String -> Maybe CScalar
canonFloat s =
  if s `elem` posInfWords then Just (CInf False)
  else if s `elem` negInfWords then Just (CInf True)
  else if s `elem` nanWords then Just CNaN
  else case unpack s of
    '+' :: cs => norm False cs
    '-' :: cs => norm True cs
    cs        => norm False cs

  where
    norm : Bool -> List Char -> Maybe CScalar
    norm neg cs = do
      (ip, fp, e) <- floatParts cs
      let (zs, ds) := span ('0' ==) (ip ++ fp)
      case reverse (dropWhile ('0' ==) (reverse ds)) of
        [] => Just CZero
        ds' =>
          Just (CSci neg (pack ds') (e + cast (length ip) - cast (length zs) - 1))

-- The canonical value of a scalar, when its tag defines one for the
-- given content; `Nothing` requests raw text comparison.
canonScalar : STag -> String -> Maybe CScalar
canonScalar TNull  s = if s `elem` nullWords then Just CNull else Nothing
canonScalar TBool  s =
  if s `elem` trueWords then Just (CBool True)
  else if s `elem` falseWords then Just (CBool False)
  else Nothing
canonScalar TInt   s = CInt <$> intVal (unpack s)
canonScalar TFloat s = canonFloat s
canonScalar _      _ = Nothing

-- Two canonicalizable contents compare by value; everything else by
-- raw text. The mixed case can only fall through to inequality:
-- `canonScalar t` is a function, so equal raw text canonicalizes
-- identically. This keeps `==` an equivalence relation.
eqScalar : STag -> String -> String -> Bool
eqScalar t a b = case (canonScalar t a, canonScalar t b) of
  (Just x, Just y) => x == y
  _                => a == b

mutual
  eqNode : Node -> Node -> Bool
  eqNode (NScalar t1 _ s1) (NScalar t2 _ s2) = t1 == t2 && eqScalar t1 s1 s2
  eqNode (NSeq t1 ns1)     (NSeq t2 ns2)     = t1 == t2 && eqNodes ns1 ns2
  eqNode (NMap t1 ps1)     (NMap t2 ps2)     = t1 == t2 && eqPairs ps1 ps2
  eqNode _                 _                 = False

  eqNodes : List Node -> List Node -> Bool
  eqNodes []        []        = True
  eqNodes (x :: xs) (y :: ys) = eqNode x y && eqNodes xs ys
  eqNodes _         _         = False

  eqPairs : List (Node, Node) -> List (Node, Node) -> Bool
  eqPairs []              []              = True
  eqPairs ((k1,v1) :: xs) ((k2,v2) :: ys) =
    eqNode k1 k2 && eqNode v1 v2 && eqPairs xs ys
  eqPairs _               _               = False

||| Node equality is tag and content [spec 3.2.1.3]: the presentation
||| style does not participate, so the plain key `a` and the quoted key
||| `"a"` are equal. Scalar content is compared by canonical value
||| where the tag defines one (`1`, `0x1` and `+1` are the same int,
||| `10.0` and `1e1` the same float), and as raw text otherwise.
export %inline
Eq Node where
  (==) = eqNode
