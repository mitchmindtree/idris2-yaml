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

||| Does a token like `-`, `?` or `:` end here, that is, is it followed
||| by white space, a line break, or the end of input?
public export
wordEnd : List Char -> Bool
wordEnd []       = True
wordEnd (c :: _) = isWhite c || isBreak c

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
  ||| Did tabs occur between the indentation and the content? Block
  ||| structure must not be preceded by tabs [spec 6.1].
  tabbed : Bool

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
    mutual
      -- at the start of a line
      line : (rem : List Char) -> Suffix False rem cs -> SkipRes cs
      line ('-' :: '-' :: '-' :: t) p =
        if wordEnd t
          then SR (L 0 LDocStart False) ('-' :: '-' :: '-' :: t) p
          else indent 0 ('-' :: '-' :: '-' :: t) p
      line ('.' :: '.' :: '.' :: t) p =
        if wordEnd t
          then SR (L 0 LDocEnd False) ('.' :: '.' :: '.' :: t) p
          else indent 0 ('.' :: '.' :: '.' :: t) p
      line rem p = indent 0 rem p

      -- counting indentation spaces
      indent : Nat -> (rem : List Char) -> Suffix False rem cs -> SkipRes cs
      indent n (' ' :: t) p = indent (S n) t (Uncons p)
      indent n rem        p = white n False rem p

      -- white space beyond the indentation (tabs are separation,
      -- not indentation)
      white : Nat -> (tb : Bool) -> (rem : List Char) -> Suffix False rem cs -> SkipRes cs
      white n tb ('\t' :: t) p = white n True t (Uncons p)
      white n tb (' '  :: t) p = white n tb t (Uncons p)
      white n tb ('\n' :: t) p = line t (Uncons p)
      white n tb ('#'  :: t) p = comment t (Uncons p)
      white n tb []          p = SR (L 0 LEnd False) [] p
      white n tb rem         p = SR (L n LContent tb) rem p

      -- the rest of a comment line
      comment : (rem : List Char) -> Suffix False rem cs -> SkipRes cs
      comment ('\n' :: t) p = line t (Uncons p)
      comment (_    :: t) p = comment t (Uncons p)
      comment []          p = SR (L 0 LEnd False) [] p

||| Result of `inlineWhite`: a count of skipped white space characters,
||| the remaining input, and a proof relating it to the original input.
public export
record Inl (cs : List Char) where
  constructor IL
  count : Nat
  ||| Was any of the white space a tab?
  tab   : Bool
  rem   : List Char
  prf   : Suffix False rem cs

||| Consumes white space within a line.
export
inlineWhite : (cs : List Char) -> Inl cs
inlineWhite cs = go 0 False cs Same

  where
    go : Nat -> Bool -> (rem : List Char) -> Suffix False rem cs -> Inl cs
    go n tb (' '  :: t) p = go (S n) tb t (Uncons p)
    go n tb ('\t' :: t) p = go (S n) True t (Uncons p)
    go n tb rem         p = IL n tb rem p

--------------------------------------------------------------------------------
--          Anchors and Tags
--------------------------------------------------------------------------------

||| May the given character occur in a URI [spec: ns-uri-char]?
public export
isUriChar : Char -> Bool
isUriChar '#'  = True
isUriChar ';'  = True
isUriChar '/'  = True
isUriChar '?'  = True
isUriChar ':'  = True
isUriChar '@'  = True
isUriChar '&'  = True
isUriChar '='  = True
isUriChar '+'  = True
isUriChar '$'  = True
isUriChar ','  = True
isUriChar '-'  = True
isUriChar '_'  = True
isUriChar '.'  = True
isUriChar '!'  = True
isUriChar '~'  = True
isUriChar '*'  = True
isUriChar '\'' = True
isUriChar '('  = True
isUriChar ')'  = True
isUriChar '['  = True
isUriChar ']'  = True
isUriChar '%'  = True
isUriChar c    = isAlphaNum c

||| A word character [spec: ns-word-char], as used in tag handles.
public export
isWordChar : Char -> Bool
isWordChar '-' = True
isWordChar c   = isAlphaNum c

||| A character of a tag shorthand's suffix [spec: ns-tag-char].
public export
isTagChar : Char -> Bool
isTagChar '!' = False
isTagChar c   = isUriChar c && not (isFlowInd c)

||| An anchor or alias name [spec: ns-anchor-name], starting at its
||| `&` or `*` indicator.
export
anchorName : Tok True YErr String
anchorName (c :: cs) = go [<] cs

  where
    go : SnocList Char -> AutoTok YErr String
    go acc (x :: xs) =
      if isPlainSafe True x
        then go (acc :< x) xs
        else case acc of
          [<] => fail p
          _   => Succ (cast acc) (x :: xs)
    go acc [] = case acc of
      [<] => fail p
      _   => Succ (cast acc) []

anchorName [] = eoiAt Same

||| A tag property [spec: c-ns-tag-property], starting at its `!`
||| indicator: verbatim (`!<...>`), a shorthand to be resolved against
||| the active tag handles, or the non-specific tag `!`.
export
tagToken : Tok True YErr (Either Tag (String, String))
tagToken ('!' :: '<' :: cs) = verb [<] cs

  where
    verb : SnocList Char -> AutoTok YErr (Either Tag (String, String))
    verb acc ('>' :: t) = case acc of
      [<] => fail p
      _   => Succ (Left (Verbatim (cast acc))) t
    verb acc ('%' :: x :: y :: t) =
      if isHexDigit x && isHexDigit y
        then verb (acc :< chr (cast $ hexDigit x * 16 + hexDigit y)) t
        else invalidEscape p t
    verb acc (x :: t)   =
      if isUriChar x then verb (acc :< x) t else fail p
    verb acc []         = eoiAt p

tagToken ('!' :: cs) = sh [<] True cs

  where
    -- the suffix after a named or secondary handle
    suff : String -> SnocList Char -> AutoTok YErr (Either Tag (String, String))
    suff h acc ('%' :: x :: y :: t) =
      if isHexDigit x && isHexDigit y
        then suff h (acc :< chr (cast $ hexDigit x * 16 + hexDigit y)) t
        else invalidEscape p t
    suff h acc (x :: t) =
      if isTagChar x && x /= '%'
        then suff h (acc :< x) t
        else case acc of
          [<] => fail p
          _   => Succ (Right (h, cast acc)) (x :: t)
    suff h acc [] = case acc of
      [<] => fail p
      _   => Succ (Right (h, cast acc)) []

    -- the shorthand: tag characters, possibly closing a handle with a
    -- second `!`
    sh : SnocList Char -> (word : Bool) -> AutoTok YErr (Either Tag (String, String))
    sh acc word ('!' :: t) =
      if word then suff ("!" ++ cast acc ++ "!") [<] t else fail p
    sh acc word ('%' :: x :: y :: t) =
      if isHexDigit x && isHexDigit y
        then sh (acc :< chr (cast $ hexDigit x * 16 + hexDigit y)) False t
        else invalidEscape p t
    sh acc word (x :: t)  =
      if isTagChar x && x /= '%'
        then sh (acc :< x) (word && isWordChar x) t
        else case acc of
          [<] => Succ (Left NonSpec) (x :: t)
          _   => Succ (Right ("!", cast acc)) (x :: t)
    sh acc word [] = case acc of
      [<] => Succ (Left NonSpec) []
      _   => Succ (Right ("!", cast acc)) []

tagToken cs = fail Same

||| A whole directive line including its line break (the break is not
||| part of the result).
export
dirLine : Tok True YErr String
dirLine (c :: cs) = go [<c] cs

  where
    go : SnocList Char -> AutoTok YErr String
    go acc ('\n' :: t) = Succ (cast acc) t
    go acc (x :: t)    = go (acc :< x) t
    go acc []          = Succ (cast acc) []

dirLine [] = eoiAt Same

--------------------------------------------------------------------------------
--          Quoted Scalars
--------------------------------------------------------------------------------

||| Is the input at a `---` or `...` document marker? Only valid at
||| column zero.
public export
isDocMarker : List Char -> Bool
isDocMarker ('-' :: '-' :: '-' :: t) = wordEnd t
isDocMarker ('.' :: '.' :: '.' :: t) = wordEnd t
isDocMarker _                        = False

-- appends k line feeds
addNl : SnocList Char -> Nat -> SnocList Char
addNl acc 0     = acc
addNl acc (S k) = addNl (acc :< '\n') k

-- the contribution of folding over k empty lines [spec: b-l-folded]
foldNl : SnocList Char -> Nat -> SnocList Char
foldNl acc 0 = acc :< ' '
foldNl acc k = addNl acc k

||| A single quoted scalar [spec: c-single-quoted], starting at its
||| opening quote. A pair of quotes escapes a quote; line breaks fold;
||| continuation lines must be indented at least `mi` spaces and must
||| not be document markers.
export
singleQuoted : (mi : Nat) -> Tok True YErr String
singleQuoted mi ('\'' :: cs) = go [<] [<] cs

  where
    mutual
      -- content within a line; pend holds white space that is dropped
      -- if the line ends
      go : (acc, pend : SnocList Char) -> AutoTok YErr String
      go acc pend ('\'' :: '\'' :: t) = go ((acc ++ pend) :< '\'') [<] t
      go acc pend ('\'' :: t)         = Succ (cast (acc ++ pend)) t
      go acc pend ('\n' :: t)         = lines acc 0 0 t
      go acc pend (' '  :: t)         = go acc (pend :< ' ') t
      go acc pend ('\t' :: t)         = go acc (pend :< '\t') t
      go acc pend (c :: t)            =
        if isControl c
          then single (InvalidControl c) p
          else go ((acc ++ pend) :< c) [<] t
      go acc pend []                  = eoiAt p

      -- at a line start: empty lines, then the next line's indentation
      lines : (acc : SnocList Char) -> (k, ind : Nat) -> AutoTok YErr String
      lines acc k ind ('\n' :: t) = lines acc (S k) 0 t
      lines acc k ind (' '  :: t) = lines acc k (S ind) t
      lines acc k ind ('\t' :: t) =
        if ind >= mi then sep acc k t else single (Custom TabIndent) p
      lines acc k ind []          = eoiAt p
      lines acc k ind (c :: t)    =
        if ind == 0 && isDocMarker (c :: t)
          then single (Unknown "document marker") p
        else if ind < mi
          then single (Custom BadIndent) p
        else go (foldNl acc k) [<] (c :: t)

      -- white space separation beyond the indentation
      sep : (acc : SnocList Char) -> (k : Nat) -> AutoTok YErr String
      sep acc k (' '  :: t) = sep acc k t
      sep acc k ('\t' :: t) = sep acc k t
      sep acc k ('\n' :: t) = lines acc (S k) 0 t
      sep acc k []          = eoiAt p
      sep acc k (c :: t)    = go (foldNl acc k) [<] (c :: t)

singleQuoted _ cs = fail Same

||| A double quoted scalar [spec: c-double-quoted], starting at its
||| opening quote: backslash escape sequences (including escaped line
||| breaks), line folding, and the same indentation and document marker
||| rules as single quoted scalars.
export
doubleQuoted : (mi : Nat) -> Tok True YErr String
doubleQuoted mi ('"' :: cs) = go [<] [<] cs

  where
    escChar : Char -> Maybe Char
    escChar '0'  = Just '\0'
    escChar 'a'  = Just '\x07'
    escChar 'b'  = Just '\b'
    escChar 't'  = Just '\t'
    escChar '\t' = Just '\t'
    escChar 'n'  = Just '\n'
    escChar 'v'  = Just '\x0b'
    escChar 'f'  = Just '\x0c'
    escChar 'r'  = Just '\r'
    escChar 'e'  = Just '\x1b'
    escChar ' '  = Just ' '
    escChar '"'  = Just '"'
    escChar '/'  = Just '/'
    escChar '\\' = Just '\\'
    escChar 'N'  = Just '\x85'
    escChar '_'  = Just '\xa0'
    escChar 'L'  = Just '\x2028'
    escChar 'P'  = Just '\x2029'
    escChar _    = Nothing

    toChar : Nat -> Maybe Char
    toChar n =
      if n > 0x10ffff || (n >= 0xd800 && n <= 0xdfff)
        then Nothing
        else Just (chr $ cast n)

    mutual
      go : (acc, pend : SnocList Char) -> AutoTok YErr String
      go acc pend ('"'  :: t)      = Succ (cast (acc ++ pend)) t
      go acc pend ('\\' :: c :: t) = case c of
        -- an escaped break: white space before it is kept, lines do
        -- not fold [spec: s-double-escaped]
        '\n' => lines (acc ++ pend) True 0 0 t
        'x'  => hex (acc ++ pend) 2 0 t
        'u'  => hex (acc ++ pend) 4 0 t
        'U'  => hex (acc ++ pend) 8 0 t
        _    => case escChar c of
          Just ch => go ((acc ++ pend) :< ch) [<] t
          Nothing => invalidEscape p t
      go acc pend ('\\' :: [])     = invalidEscape p []
      go acc pend ('\n' :: t)      = lines acc False 0 0 t
      go acc pend (' '  :: t)      = go acc (pend :< ' ') t
      go acc pend ('\t' :: t)      = go acc (pend :< '\t') t
      go acc pend (c :: t)         =
        if isControl c
          then single (InvalidControl c) p
          else go ((acc ++ pend) :< c) [<] t
      go acc pend []               = eoiAt p

      -- a fixed number of hex digits of a character escape
      hex : (acc : SnocList Char) -> (k, val : Nat) -> AutoTok YErr String
      hex acc 0     val cs2 = case toChar val of
        Just ch => go (acc :< ch) [<] cs2
        Nothing => invalidEscape p cs2
      hex acc (S k) val (c :: t) =
        if isHexDigit c
          then hex acc k (val * 16 + hexDigit c) t
          else invalidEscape p t
      hex acc (S k) val [] = eoiAt p

      -- at a line start; `eb` is true after an escaped break, which
      -- suppresses the folding space
      lines : (acc : SnocList Char) -> (eb : Bool) -> (k, ind : Nat) -> AutoTok YErr String
      lines acc eb k ind ('\n' :: t) = lines acc eb (S k) 0 t
      lines acc eb k ind (' '  :: t) = lines acc eb k (S ind) t
      lines acc eb k ind ('\t' :: t) =
        if ind >= mi then sep acc eb k t else single (Custom TabIndent) p
      lines acc eb k ind []          = eoiAt p
      lines acc eb k ind (c :: t)    =
        if ind == 0 && isDocMarker (c :: t)
          then single (Unknown "document marker") p
        else if ind < mi
          then single (Custom BadIndent) p
        else go (if eb then addNl acc k else foldNl acc k) [<] (c :: t)

      -- white space separation beyond the indentation
      sep : (acc : SnocList Char) -> (eb : Bool) -> (k : Nat) -> AutoTok YErr String
      sep acc eb k (' '  :: t) = sep acc eb k t
      sep acc eb k ('\t' :: t) = sep acc eb k t
      sep acc eb k ('\n' :: t) = lines acc eb (S k) 0 t
      sep acc eb k []          = eoiAt p
      sep acc eb k (c :: t)    = go (if eb then addNl acc k else foldNl acc k) [<] (c :: t)

doubleQuoted _ cs = fail Same

--------------------------------------------------------------------------------
--          Block Scalars
--------------------------------------------------------------------------------

||| Chomping of a block scalar's trailing line breaks
||| [spec: c-chomping-indicator].
public export
data Chomp = Strip | Clip | Keep

||| A block scalar [spec: c-l+literal, c-l+folded], starting at its `|`
||| or `>` indicator: the header (indentation and chomping indicators
||| plus an optional comment), then the indented content lines.
|||
||| `mi` is the minimum content indentation, that is, the parent
||| node's indentation plus one; an explicit indentation indicator `d`
||| anchors the content at `mi + d - 1` columns.
export
blockScalar : (folded : Bool) -> (mi : Nat) -> Tok True YErr String
blockScalar folded mi (c :: cs) = hdr Nothing Nothing cs

  where
    -- assembles the final scalar from the accumulated content and the
    -- pending trailing line breaks
    fin : Chomp -> (acc : SnocList Char) -> (brk : Nat) -> String
    fin Strip acc _   = cast acc
    fin Keep  acc brk = cast (addNl acc brk)
    fin Clip  acc brk = case acc of
      [<] => ""
      _   => if brk > 0 then cast (acc :< '\n') else cast acc

    -- the contribution of a content line: pending breaks (folded where
    -- applicable), then the line itself [spec: b-l-folded]
    contrib :
         (prev : Maybe Bool)   -- spacedness of the previous line, if any
      -> (brk : Nat)           -- pending line breaks
      -> (spaced : Bool)       -- does this line start with white space?
      -> (acc, line : SnocList Char)
      -> SnocList Char
    contrib prev brk spaced acc line =
      let joined := case prev of
            Nothing => addNl acc brk
            Just pSp =>
              if folded && not pSp && not spaced
                then (if brk == 1 then acc :< ' ' else addNl acc (brk `minus` 1))
                else addNl acc brk
       in joined ++ line

    -- the content indentation: fixed (explicit or detected), or still
    -- to be detected (tracking the deepest empty line seen so far)
    data Ci = Fixed Nat | Auto Nat

    -- classification of the next line, without consuming it: an empty
    -- line, white space before the end of input, or content (with a
    -- document marker or tab flag)
    data PLine = PBlank Nat | PEnd Nat | PCont Nat Bool Bool

    peek : Nat -> List Char -> PLine
    peek n (' '  :: t) = peek (S n) t
    peek n ('\n' :: _) = PBlank n
    peek n []          = PEnd n
    peek n cs2@(x :: _) = PCont n (n == 0 && isDocMarker cs2) (x == '\t')

    startCi : Maybe Nat -> Ci
    startCi Nothing  = Auto 0
    startCi (Just d) = Fixed ((mi + d) `minus` 1)

    mutual
      -- at a line start: decide whether the next line still belongs to
      -- the scalar before consuming anything
      atLine :
           Chomp -> Ci -> (prev : Maybe Bool) -> (acc : SnocList Char)
        -> (brk : Nat) -> AutoTok YErr String
      atLine ch ci prev acc brk cs2 = case peek 0 cs2 of
        PEnd n => case ci of
          -- trailing white space before the end of input: a content
          -- line of spaces if more indented, an empty line otherwise
          Fixed n2 =>
            if n > n2
              then capture ch n2 prev acc brk 0 [<] cs2
              else Succ (fin ch acc (if n > 0 then S brk else brk)) cs2
          Auto _ => Succ (fin ch acc (if n > 0 then S brk else brk)) cs2
        PBlank n => case ci of
          Auto mb => blank ch (Auto $ max mb n) prev acc brk cs2
          Fixed n2 =>
            if n > n2
              then capture ch n2 prev acc brk 0 [<] cs2
              else blank ch (Fixed n2) prev acc brk cs2
        PCont n marker tab => case ci of
          Auto mb =>
            if tab && n < mi
              then range (Custom TabIndent) p cs2
            else if n < mi || marker
              then Succ (fin ch acc brk) cs2
            else if mb > n
              then fail Same
            else capture ch n prev acc brk 0 [<] cs2
          Fixed n2 =>
            if tab && n < n2
              then range (Custom TabIndent) p cs2
            else if n < n2 || marker
              then Succ (fin ch acc brk) cs2
              else capture ch n2 prev acc brk 0 [<] cs2

      -- consumes an empty line
      blank :
           Chomp -> Ci -> (prev : Maybe Bool) -> (acc : SnocList Char)
        -> (brk : Nat) -> AutoTok YErr String
      blank ch ci prev acc brk (' '  :: t) = blank ch ci prev acc brk t
      blank ch ci prev acc brk ('\n' :: t) = atLine ch ci prev acc (S brk) t
      blank ch ci prev acc brk (_ :: t)    = fail Same
      blank ch ci prev acc brk []          = Succ (fin ch acc brk) []

      -- consumes a content line: its indentation (spaces beyond the
      -- content indent are content), then the raw text
      capture :
           Chomp -> (n : Nat) -> (prev : Maybe Bool) -> (acc : SnocList Char)
        -> (brk, m : Nat) -> (line : SnocList Char) -> AutoTok YErr String
      capture ch n prev acc brk m line (' ' :: t) =
        if m >= n
          then capture ch n prev acc brk (S m) (line :< ' ') t
          else capture ch n prev acc brk (S m) line t
      capture ch n prev acc brk m line ('\t' :: t) =
        if m >= n
          then capLine ch n prev acc brk True (line :< '\t') t
          else single (Custom TabIndent) p
      capture ch n prev acc brk m line ('\n' :: t) =
        let spaced := m > n
         in atLine ch (Fixed n) (Just spaced) (contrib prev brk spaced acc line) 1 t
      capture ch n prev acc brk m line [] =
        -- a content line ending at the end of input still counts as
        -- ended by a break for chomping [spec: b-chomped-last]
        let spaced := m > n
         in Succ (fin ch (contrib prev brk spaced acc line) 1) []
      capture ch n prev acc brk m line (x :: t) =
        if isControl x
          then single (InvalidControl x) p
          else capLine ch n prev acc brk (m > n) (line :< x) t

      -- the raw remainder of a content line
      capLine :
           Chomp -> (n : Nat) -> (prev : Maybe Bool) -> (acc : SnocList Char)
        -> (brk : Nat) -> (spaced : Bool) -> (line : SnocList Char)
        -> AutoTok YErr String
      capLine ch n prev acc brk spaced line ('\n' :: t) =
        atLine ch (Fixed n) (Just spaced) (contrib prev brk spaced acc line) 1 t
      capLine ch n prev acc brk spaced line (x :: t) =
        if isControl x && x /= '\t'
          then single (InvalidControl x) p
          else capLine ch n prev acc brk spaced (line :< x) t
      capLine ch n prev acc brk spaced line [] =
        Succ (fin ch (contrib prev brk spaced acc line) 1) []

      -- the header: at most one indentation digit and one chomping
      -- indicator, optional comment, then the first line break
      hdr : (d : Maybe Nat) -> (ch : Maybe Chomp) -> AutoTok YErr String
      hdr d ch ('-' :: t)  = case ch of
        Nothing => hdr d (Just Strip) t
        Just _  => fail Same
      hdr d ch ('+' :: t)  = case ch of
        Nothing => hdr d (Just Keep) t
        Just _  => fail Same
      hdr d ch ('\n' :: t) = atLine (maybe Clip id ch) (startCi d) Nothing [<] 0 t
      hdr d ch (' '  :: t) = hdrEnd d ch t
      hdr d ch ('\t' :: t) = hdrEnd d ch t
      hdr d ch []          = Succ (fin (maybe Clip id ch) [<] 0) []
      hdr d ch (x :: t)    =
        if isDigit x && x /= '0'
          then case d of
            Nothing => hdr (Just $ digit x) ch t
            Just _  => fail Same
          else fail Same

      -- after the header's indicators: separation and a comment
      hdrEnd : (d : Maybe Nat) -> (ch : Maybe Chomp) -> AutoTok YErr String
      hdrEnd d ch (' '  :: t) = hdrEnd d ch t
      hdrEnd d ch ('\t' :: t) = hdrEnd d ch t
      hdrEnd d ch ('#'  :: t) = hdrCom d ch t
      hdrEnd d ch ('\n' :: t) = atLine (maybe Clip id ch) (startCi d) Nothing [<] 0 t
      hdrEnd d ch []          = Succ (fin (maybe Clip id ch) [<] 0) []
      hdrEnd d ch (x :: t)    = fail Same

      -- the header's comment
      hdrCom : (d : Maybe Nat) -> (ch : Maybe Chomp) -> AutoTok YErr String
      hdrCom d ch ('\n' :: t) = atLine (maybe Clip id ch) (startCi d) Nothing [<] 0 t
      hdrCom d ch (_ :: t)    = hdrCom d ch t
      hdrCom d ch []          = Succ (fin (maybe Clip id ch) [<] 0) []

blockScalar _ _ [] = eoiAt Same

--------------------------------------------------------------------------------
--          Plain Scalars
--------------------------------------------------------------------------------

||| Continuation of a plain scalar onto the next line (see `plainCont`).
public export
data Cont : (cs : List Char) -> Type where
  ||| The scalar ends here: nothing is consumed.
  Stop : Cont cs

  ||| The scalar continues at `rem`, with `blanks` empty lines between
  ||| the segments (zero empty lines fold into a single space).
  More : (blanks : Nat) -> (rem : List Char) -> Suffix True rem cs -> Cont cs

||| From the end of a plain-scalar segment (at its trailing white space
||| or line break): does the scalar continue on a following line
||| [spec: s-flow-folded]?
|||
||| Stops at comment lines, document markers, lines indented less than
||| `mi`, and lines starting with a character that cannot continue a
||| plain scalar. This must mirror the stop conditions of
||| `plainSegment`'s lookahead.
export
plainCont : (inFlow : Bool) -> (mi : Nat) -> (cs : List Char) -> Cont cs
plainCont inFlow mi cs = pre cs Same

  where
    isMarker : List Char -> Bool
    isMarker ('-' :: '-' :: '-' :: t) = wordEnd t
    isMarker ('.' :: '.' :: '.' :: t) = wordEnd t
    isMarker _                        = False

    -- may a continuation line start with this content [spec:
    -- ns-plain-char]?
    contFirst : Char -> List Char -> Bool
    contFirst '#' _        = False
    contFirst ':' (n :: _) = isPlainSafe inFlow n
    contFirst ':' []       = False
    contFirst c   _        = not (inFlow && isFlowInd c)

    mutual
      -- at the start of a line (the first break already consumed)
      line : Nat -> (rem : List Char) -> Suffix True rem cs -> Cont cs
      line k rem p = if isMarker rem then Stop else indent k 0 rem p

      -- counting indentation spaces
      indent : Nat -> Nat -> (rem : List Char) -> Suffix True rem cs -> Cont cs
      indent k n (' ' :: t) p = indent k (S n) t (Uncons p)
      indent k n rem        p = white k n rem p

      -- separation white space beyond the indentation
      white : Nat -> Nat -> (rem : List Char) -> Suffix True rem cs -> Cont cs
      white k n ('\t' :: t) p = white k n t (Uncons p)
      white k n (' '  :: t) p = white k n t (Uncons p)
      white k n ('\n' :: t) p = line (S k) t (Uncons p)
      white k n []          p = Stop
      white k n (c :: t)    p =
        if n >= mi && contFirst c t then More k (c :: t) p else Stop

    -- white space before the first line break
    pre : (rem : List Char) -> Suffix False rem cs -> Cont cs
    pre (' '  :: t) p = pre t (Uncons p)
    pre ('\t' :: t) p = pre t (Uncons p)
    pre ('\n' :: t) p = line 0 t (Uncons p)
    pre _           p = Stop

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
