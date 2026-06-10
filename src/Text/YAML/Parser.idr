module Text.YAML.Parser

import public Text.Parse.Manual
import public Text.YAML.Types
import Text.YAML.Lexer

%default total

--------------------------------------------------------------------------------
--          Parser State
--------------------------------------------------------------------------------

||| State threaded through all parsing rules: the current position in
||| the input and the events emitted so far.
public export
record YState where
  constructor YS
  pos : Position
  evs : SnocList Event

%inline
emit : Event -> YState -> YState
emit e = {evs $= (:< e)}

||| An empty node, e.g. the missing value in `key:` [spec: e-scalar].
%inline
emptyScalar : SnocList Event -> SnocList Event
emptyScalar = (:< Scalar Nothing NoTag Plain "")

--------------------------------------------------------------------------------
--          Rule Type
--------------------------------------------------------------------------------

||| A parsing rule, consuming a prefix of the remaining input (a strict
||| one if `b` is `True`).
|||
||| Totality: all recursion in the rules below runs over the strictly
||| shrinking character list via `SuffixAcc`. Since some nodes may be
||| empty (consuming nothing), every loop derives its strictness from a
||| separator it consumed itself (a comma, colon, dash, or line break)
||| before recursing.
public export
0 Rule : Bool -> Type -> Type
Rule b a =
     YState
  -> (cs : List Char)
  -> (0 acc : SuffixAcc cs)
  -> Result0 b Char cs (BoundedErr YErr) a

--------------------------------------------------------------------------------
--          Separation in Flow Context
--------------------------------------------------------------------------------

-- Blank and comment lines between flow tokens: continuation lines must
-- not be document markers and must be indented at least `mi` spaces.
flowLines :
     (tok : String)
  -> (b : Bounds)
  -> (mi : Nat)
  -> Position
  -> (cs : List Char)
  -> Result0 False Char cs (BoundedErr YErr) Position
flowLines tok b mi pos cs = case skipToContent cs of
  SR (L _   LEnd)     rem prf => Succ0 (endPos pos prf) rem @{prf}
  SR (L ind LContent) rem prf =>
    if ind >= mi
      then Succ0 (endPos pos prf) rem @{prf}
      else custom (oneChar $ endPos pos prf) BadIndent
  SR (L _ _) rem prf => unclosed b tok

-- A comment within flow content: consumes the rest of the line.
flowComment :
     (tok : String)
  -> (b : Bounds)
  -> (mi : Nat)
  -> Position
  -> (cs : List Char)
  -> Result0 False Char cs (BoundedErr YErr) Position
flowComment tok b mi pos (c :: cs) =
  if isBreak c
    then succF $ flowLines tok b mi (incLine pos) cs
    else succF $ flowComment tok b mi (incCol pos) cs
flowComment _ _ _ pos [] = Succ0 pos []

||| Skips separation white space, comments and line breaks between flow
||| tokens [spec: s-separate]. A `#` starts a comment only when preceded
||| by white space or a line break (`sw` tracks whether white space was
||| already seen).
flowSkip :
     (tok : String)
  -> (b : Bounds)
  -> (mi : Nat)
  -> (sw : Bool)
  -> Position
  -> (cs : List Char)
  -> Result0 False Char cs (BoundedErr YErr) Position
flowSkip tok b mi sw pos (c :: cs) =
  if isWhite c then succF $ flowSkip tok b mi True (incCol pos) cs
  else if isBreak c then succF $ flowLines tok b mi (incLine pos) cs
  else if c == '#' && sw then succF $ flowComment tok b mi (incCol pos) cs
  else Succ0 pos (c :: cs)
flowSkip _ _ _ _ pos [] = Succ0 pos []

--------------------------------------------------------------------------------
--          Flow Nodes
--------------------------------------------------------------------------------

-- Spec context note: `inFlow` distinguishes the FLOW-IN/FLOW-KEY
-- contexts (inside a flow collection) from FLOW-OUT/BLOCK-* (outside),
-- which changes where plain scalars end. `mi` is the minimum number of
-- indentation spaces for continuation lines (the spec's `n + 1`).

plainSafeNext : List Char -> Bool
plainSafeNext (c :: _) = isPlainSafe True c
plainSafeNext []       = False

mutual
  ||| A single flow node [spec: ns-flow-node]: a plain scalar or a flow
  ||| collection. Expects the input to be at a content character.
  flowNode : (inFlow : Bool) -> (mi : Nat) -> Rule True YState
  flowNode inFlow mi st [] _ = eoi
  flowNode inFlow mi st (c :: cs) (SA r) = case c of
    '[' => case flowSkip "[" (oneChar st.pos) mi False (incCol st.pos) cs of
      Fail0 e => Fail0 e
      Succ0 p1 r1 @{q1} =>
        let 0 pp := trans q1 (uncons Same)
            st1  := YS p1 (st.evs :< SeqStart True Nothing NoTag)
         in succT (flowSeq mi (oneChar st.pos) st1 r1 (r @{pp})) @{pp}
    '{' => case flowSkip "{" (oneChar st.pos) mi False (incCol st.pos) cs of
      Fail0 e => Fail0 e
      Succ0 p1 r1 @{q1} =>
        let 0 pp := trans q1 (uncons Same)
            st1  := YS p1 (st.evs :< MapStart True Nothing NoTag)
         in succT (flowMap mi (oneChar st.pos) st1 r1 (r @{pp})) @{pp}
    _   =>
      if isPlainFirst inFlow c cs
        then case plainSegment inFlow (c :: cs) of
          Succ s rem @{prf} =>
            Succ0 (YS (move st.pos prf) (st.evs :< Scalar Nothing NoTag Plain s)) rem
          Fail start errEnd err => Fail0 (boundedErr st.pos start errEnd err)
        else parseFail (oneChar st.pos) (Unknown $ pack [c])

  ||| Inside a flow sequence [spec: c-flow-sequence], at a content
  ||| character: an entry or the closing bracket. The loop consumes the
  ||| separating comma itself before recursing.
  flowSeq : (mi : Nat) -> (b : Bounds) -> Rule True YState
  flowSeq mi b st (']' :: cs) _ = Succ0 (emit SeqEnd $ {pos $= incCol} st) cs
  flowSeq mi b st []          _ = unclosed b "["
  flowSeq mi b st l sa@(SA r)   =
    case flowNode True mi st l sa of
      Fail0 e => Fail0 e
      Succ0 st1 r1 @{q1} => case flowSkip "[" b mi False st1.pos r1 of
        Fail0 e => Fail0 e
        Succ0 p2 (']' :: r2) @{q2} =>
          Succ0 (YS (incCol p2) (st1.evs :< SeqEnd)) r2
            @{trans (uncons Same) (trans q2 q1)}
        Succ0 p2 (',' :: r2) @{q2} =>
          case flowSkip "[" b mi False (incCol p2) r2 of
            Fail0 e => Fail0 e
            Succ0 p3 r3 @{q3} =>
              let 0 pp := trans q3 (trans (uncons Same) (trans q2 q1))
               in succT (flowSeq mi b (YS p3 st1.evs) r3 (r @{pp})) @{pp}
        Succ0 p2 [] => unclosed b "["
        Succ0 p2 (x :: _) =>
          parseFail (oneChar p2) (Expected ["','", "']'"] (pack [x]))

  ||| Inside a flow mapping [spec: c-flow-mapping], at a content
  ||| character: an entry or the closing brace.
  flowMap : (mi : Nat) -> (b : Bounds) -> Rule True YState
  flowMap mi b st ('}' :: cs) _ = Succ0 (emit MapEnd $ {pos $= incCol} st) cs
  flowMap mi b st []          _ = unclosed b "{"
  flowMap mi b st (c :: cs) sa@(SA r) =
    if c == ':' && not (plainSafeNext cs)
      then -- an entry with an empty key [spec: c-ns-flow-map-empty-key-entry]
        case flowSkip "{" b mi False (incCol st.pos) cs of
          Fail0 e => Fail0 e
          Succ0 p1 r1 @{q1} =>
            let 0 pp := trans q1 (uncons Same)
             in case flowVal mi (YS p1 (emptyScalar st.evs)) r1 (r @{pp}) of
                  Fail0 e => Fail0 e
                  Succ0 st2 r2 @{q2} => case flowSkip "{" b mi False st2.pos r2 of
                    Fail0 e => Fail0 e
                    Succ0 p3 r3 @{q3} =>
                      let 0 pp3 := trans (trans q3 (trans q2 q1)) (uncons Same)
                       in succT (mapTail mi b (YS p3 st2.evs) r3 (r @{pp3})) @{pp3}
      else -- an entry starting with a key node
        case flowNode True mi st (c :: cs) sa of
          Fail0 e => Fail0 e
          Succ0 st1 r1 @{q1} => case flowSkip "{" b mi False st1.pos r1 of
            Fail0 e => Fail0 e
            Succ0 p2 (':' :: r2) @{q2} =>
              case flowSkip "{" b mi False (incCol p2) r2 of
                Fail0 e => Fail0 e
                Succ0 p3 r3 @{q3} =>
                  let 0 pp := trans q3 (trans (uncons Same) (trans q2 q1))
                   in case flowVal mi (YS p3 st1.evs) r3 (r @{pp}) of
                        Fail0 e => Fail0 e
                        Succ0 st4 r4 @{q4} =>
                          case flowSkip "{" b mi False st4.pos r4 of
                            Fail0 e => Fail0 e
                            Succ0 p5 r5 @{q5} =>
                              let 0 pp5 := trans q5 (trans q4 pp)
                               in succT (mapTail mi b (YS p5 st4.evs) r5 (r @{pp5})) @{pp5}
            Succ0 p2 r2 @{q2} =>
              -- no colon: the value is empty [spec: ns-flow-map-yaml-key-entry]
              let 0 pp := trans q2 q1
               in succT (mapTail mi b (YS p2 (emptyScalar st1.evs)) r2 (r @{pp})) @{pp}

  ||| The value of a flow mapping entry, after its `:` indicator and
  ||| any separation: empty if the entry ends here.
  flowVal : (mi : Nat) -> Rule False YState
  flowVal mi st []          _   = Succ0 ({evs $= emptyScalar} st) []
  flowVal mi st (',' :: cs) _   = Succ0 ({evs $= emptyScalar} st) (',' :: cs)
  flowVal mi st ('}' :: cs) _   = Succ0 ({evs $= emptyScalar} st) ('}' :: cs)
  flowVal mi st cs          acc = weaken $ flowNode True mi st cs acc

  ||| After a complete flow mapping entry: a comma followed by the next
  ||| entry, or the closing brace.
  mapTail : (mi : Nat) -> (b : Bounds) -> Rule True YState
  mapTail mi b st ('}' :: cs) _ = Succ0 (emit MapEnd $ {pos $= incCol} st) cs
  mapTail mi b st (',' :: cs) (SA r) =
    case flowSkip "{" b mi False (incCol st.pos) cs of
      Fail0 e => Fail0 e
      Succ0 p1 r1 @{q1} =>
        let 0 pp := trans q1 (uncons Same)
         in succT (flowMap mi b (YS p1 st.evs) r1 (r @{pp})) @{pp}
  mapTail mi b st []          _ = unclosed b "{"
  mapTail mi b st (x :: _)    _ =
    parseFail (oneChar st.pos) (Expected ["','", "'}'"] (pack [x]))

--------------------------------------------------------------------------------
--          Documents
--------------------------------------------------------------------------------

-- Blank and comment lines after a document's root node: only the end
-- of input may follow (single-document subset).
docLines : Position -> (cs : List Char) -> Result0 False Char cs (BoundedErr YErr) Position
docLines pos cs = case skipToContent cs of
  SR (L _ LEnd) rem prf => Succ0 (endPos pos prf) rem @{prf}
  SR (L _ _)    rem prf => custom (oneChar $ endPos pos prf) TrailingContent

-- A comment after a document's root node.
docComment : Position -> (cs : List Char) -> Result0 False Char cs (BoundedErr YErr) Position
docComment pos (c :: cs) =
  if isBreak c
    then succF $ docLines (incLine pos) cs
    else succF $ docComment (incCol pos) cs
docComment pos [] = Succ0 pos []

||| Consumes trailing white space and comments after a document's root
||| node, succeeding only if the end of input follows.
trailer : (sw : Bool) -> Position -> (cs : List Char) -> Result0 False Char cs (BoundedErr YErr) Position
trailer sw pos (c :: cs) =
  if isWhite c then succF $ trailer True (incCol pos) cs
  else if isBreak c then succF $ docLines (incLine pos) cs
  else if c == '#' && sw then succF $ docComment (incCol pos) cs
  else custom (oneChar pos) TrailingContent
trailer _ pos [] = Succ0 pos []

||| A single document: leading blank and comment lines, an optional
||| root node, trailing blank and comment lines.
doc : Rule False YState
doc st cs sa@(SA r) = case skipToContent cs of
  SR (L _ LEnd)     rem prf => Succ0 ({pos := endPos st.pos prf} st) rem @{prf}
  SR (L _ LContent) rem prf =>
    let st1 := YS (endPos st.pos prf) (st.evs :< DocStart False)
     in case prf of
          Same     => content st1 cs sa
          Uncons u => trans (content st1 rem (r @{uncons u})) (weaken $ uncons u)
  SR (L _ _)        rem prf =>
    parseFail (oneChar $ endPos st.pos prf) (Unknown "document marker")

  where
    content :
         YState
      -> (rem : List Char)
      -> (0 acc : SuffixAcc rem)
      -> Result0 False Char rem (BoundedErr YErr) YState
    content st1 rem acc = case flowNode False 0 st1 rem acc of
      Fail0 e => Fail0 e
      Succ0 st2 r2 @{q} =>
        case trailer False st2.pos r2 of
          Fail0 e => Fail0 e
          Succ0 p3 r3 @{q3} =>
            Succ0 (YS p3 (st2.evs :< DocEnd False)) r3 @{weaken $ trans q3 q}

--------------------------------------------------------------------------------
--          Entry Point
--------------------------------------------------------------------------------

||| Line break normalization [spec 5.4]: CRLF and lone CR become LF.
||| A leading byte order mark is dropped.
normalize : List Char -> List Char
normalize ('\r' :: '\n' :: cs) = '\n' :: normalize cs
normalize ('\r' :: cs)         = '\n' :: normalize cs
normalize (c :: cs)            = c    :: normalize cs
normalize []                   = []

||| Parses a complete YAML stream into its sequence of events.
export
parseEvents : Origin -> String -> Either (ParseError YErr) (List Event)
parseEvents o str =
  let cs := normalize (stripBom $ unpack str)
   in case doc (YS begin [<StreamStart]) cs suffixAcc of
        Succ0 st _ => Right (st.evs <>> [StreamEnd])
        Fail0 err  => Left (toParseError o (pack cs) err)

  where
    stripBom : List Char -> List Char
    stripBom ('\xfeff' :: cs) = cs
    stripBom cs               = cs
