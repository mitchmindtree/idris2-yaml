module Text.YAML.Lexer

import public Text.Lex.Manual
import Text.YAML.Types

%default total

--------------------------------------------------------------------------------
--          Character Classes
--------------------------------------------------------------------------------

||| A line break. Input is normalized before parsing (see
||| `Text.YAML.Parser.parseEvents`), so only line feeds occur [spec 5.4].
public export %inline
isBreak : Char -> Bool
isBreak '\n' = True
isBreak _    = False

||| White space within a line [spec: s-white].
public export %inline
isWhite : Char -> Bool
isWhite ' '  = True
isWhite '\t' = True
isWhite _    = False

||| A flow collection indicator [spec: c-flow-indicator].
public export
isFlowInd : Char -> Bool
isFlowInd ',' = True
isFlowInd '[' = True
isFlowInd ']' = True
isFlowInd '{' = True
isFlowInd '}' = True
isFlowInd _   = False

||| A character that cannot start a plain scalar [spec: c-indicator].
public export
isIndicator : Char -> Bool
isIndicator '-'  = True
isIndicator '?'  = True
isIndicator ':'  = True
isIndicator '#'  = True
isIndicator '&'  = True
isIndicator '*'  = True
isIndicator '!'  = True
isIndicator '|'  = True
isIndicator '>'  = True
isIndicator '\'' = True
isIndicator '"'  = True
isIndicator '%'  = True
isIndicator '@'  = True
isIndicator '`'  = True
isIndicator c    = isFlowInd c

||| A character that may occur in the middle of a plain scalar
||| [spec: ns-plain-safe]. In flow context, flow indicators end a
||| plain scalar.
public export
isPlainSafe : (inFlow : Bool) -> Char -> Bool
isPlainSafe inFlow c =
  not (isWhite c || isBreak c || isControl c || (inFlow && isFlowInd c))

||| May the given character start a plain scalar when followed by the
||| given remainder [spec: ns-plain-first]?
public export
isPlainFirst : (inFlow : Bool) -> Char -> List Char -> Bool
isPlainFirst inFlow '-' (c :: _) = isPlainSafe inFlow c
isPlainFirst inFlow '?' (c :: _) = isPlainSafe inFlow c
isPlainFirst inFlow ':' (c :: _) = isPlainSafe inFlow c
isPlainFirst inFlow c   _        =
  not (isIndicator c || isWhite c || isBreak c || isControl c)

--------------------------------------------------------------------------------
--          Line Structure
--------------------------------------------------------------------------------

||| Classification of the next content found by `skipToContent`.
public export
data LineKind : Type where
  ||| A line holding regular content.
  LContent  : LineKind

  ||| A `---` document marker at column zero.
  LDocStart : LineKind

  ||| A `...` document marker at column zero.
  LDocEnd   : LineKind

  ||| The end of the input.
  LEnd      : LineKind

public export
record Look where
  constructor L
  ||| Number of indentation spaces before the content. Only meaningful
  ||| for `LContent`.
  indent : Nat
  kind   : LineKind

||| Result of `skipToContent`: the classification of what follows, the
||| remaining input, and a proof relating it to the original input.
public export
record SkipRes (cs : List Char) where
  constructor SR
  look : Look
  rem  : List Char
  prf  : Suffix False rem cs

||| Consumes blank and comment-only lines, classifying what follows.
|||
||| Must be called at the start of a line. Document markers (at column
||| zero) and the end of input are reported without consuming them. For
||| a content line, the leading indentation (and any further white
||| space separation before the first content character) is consumed
||| and the number of indentation spaces is reported. Tabs never count
||| as indentation [spec 6.1].
export
skipToContent : (cs : List Char) -> SkipRes cs
skipToContent cs = line cs Same

  where
    wordEnd : List Char -> Bool
    wordEnd []       = True
    wordEnd (c :: _) = isWhite c || isBreak c

    mutual
      -- at the start of a line
      line : (rem : List Char) -> Suffix False rem cs -> SkipRes cs
      line ('-' :: '-' :: '-' :: t) p =
        if wordEnd t
          then SR (L 0 LDocStart) ('-' :: '-' :: '-' :: t) p
          else indent 0 ('-' :: '-' :: '-' :: t) p
      line ('.' :: '.' :: '.' :: t) p =
        if wordEnd t
          then SR (L 0 LDocEnd) ('.' :: '.' :: '.' :: t) p
          else indent 0 ('.' :: '.' :: '.' :: t) p
      line rem p = indent 0 rem p

      -- counting indentation spaces
      indent : Nat -> (rem : List Char) -> Suffix False rem cs -> SkipRes cs
      indent n (' ' :: t) p = indent (S n) t (Uncons p)
      indent n rem        p = white n rem p

      -- white space beyond the indentation (tabs are separation,
      -- not indentation)
      white : Nat -> (rem : List Char) -> Suffix False rem cs -> SkipRes cs
      white n ('\t' :: t) p = white n t (Uncons p)
      white n (' '  :: t) p = white n t (Uncons p)
      white n ('\n' :: t) p = line t (Uncons p)
      white n ('#'  :: t) p = comment t (Uncons p)
      white n []          p = SR (L 0 LEnd) [] p
      white n rem         p = SR (L n LContent) rem p

      -- the rest of a comment line
      comment : (rem : List Char) -> Suffix False rem cs -> SkipRes cs
      comment ('\n' :: t) p = line t (Uncons p)
      comment (_    :: t) p = comment t (Uncons p)
      comment []          p = SR (L 0 LEnd) [] p

--------------------------------------------------------------------------------
--          Plain Scalars
--------------------------------------------------------------------------------

||| A single line's worth of a plain scalar [spec: ns-plain-one-line],
||| assuming the first character of the input starts a plain scalar
||| (see `isPlainFirst`; verified by the caller).
|||
||| Stops without consuming at the scalar's end: the end of the line, a
||| ` #` comment, a `:` followed by white space (or, in flow context, a
||| flow indicator or the end of the line), or, in flow context, any
||| flow indicator. Trailing white space is neither part of the result
||| nor consumed.
export
plainSegment : (inFlow : Bool) -> Tok True YErr String
plainSegment inFlow (c :: cs) =
  if isControl c then single (InvalidControl c) Same else go [<c] cs

  where
    -- is a `:` at this point part of the scalar rather than a value
    -- indicator [spec: ns-plain-char]?
    colonCont : List Char -> Bool
    colonCont (n :: _) = isPlainSafe inFlow n
    colonCont []       = False

    -- non-consuming lookahead: may the scalar continue beyond a run
    -- of white space?
    cont : List Char -> Bool
    cont (x :: xs) =
      if isWhite x then cont xs
      else if isBreak x then False
      else case x of
        '#' => False
        ':' => colonCont xs
        _   => not (inFlow && isFlowInd x)
    cont [] = False

    go : SnocList Char -> AutoTok YErr String
    go acc []        = Succ (cast acc) []
    go acc (x :: xs) =
      if isWhite x then
        if cont xs then go (acc :< x) xs else Succ (cast acc) (x :: xs)
      else if isBreak x then Succ (cast acc) (x :: xs)
      else if x == ':' then
        if colonCont xs
          then go (acc :< ':') xs
          else Succ (cast acc) (x :: xs)
      else if inFlow && isFlowInd x then Succ (cast acc) (x :: xs)
      else if isControl x then single (InvalidControl x) p
      else go (acc :< x) xs

plainSegment _ [] = eoiAt Same
