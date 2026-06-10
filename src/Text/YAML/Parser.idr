module Text.YAML.Parser

import Data.String
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

||| An inline node candidate for implicit-key detection: a single-line
||| plain scalar (its event not yet emitted, since it might yet grow by
||| line folding), or a flow collection parsed into its own event
||| buffer.
data Pending : Type where
  PScalar : String -> Pending
  PFlow   : SnocList Event -> Pending

flushPend : SnocList Event -> Pending -> SnocList Event
flushPend evs (PScalar s) = evs :< Scalar Nothing NoTag Plain s
flushPend evs (PFlow d)   = evs ++ d

-- Is the next token a `:` value indicator in block context?
colonBlock : List Char -> Bool
colonBlock (':' :: t) = wordEnd t
colonBlock _          = False

-- Is the next token a `:` value indicator in flow context?
colonFlow : List Char -> Bool
colonFlow (':' :: n :: _) = not (isPlainSafe True n)
colonFlow (':' :: [])     = True
colonFlow _               = False

-- Does a `- ` sequence entry indicator follow?
dashNext : List Char -> Bool
dashNext ('-' :: t) = wordEnd t
dashNext _          = False

plainSafeNext : List Char -> Bool
plainSafeNext (c :: _) = isPlainSafe True c
plainSafeNext []       = False

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
||| before recursing. Lookahead over blank and comment lines
||| (`skipToContent`) returns a non-erased, possibly-empty `Suffix`:
||| where a rule continues after such a skip, it matches `Same`/`Uncons`
||| explicitly so the recursion goes through a projection of its
||| `SuffixAcc` argument.
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
--          Line Ends in Block Context
--------------------------------------------------------------------------------

-- The rest of a `lineEnd` comment.
lineEndC : Position -> (cs : List Char) -> Result0 False Char cs (BoundedErr YErr) Position
lineEndC pos [] = Succ0 pos []
lineEndC pos (c :: cs) =
  if isBreak c
    then Succ0 pos (c :: cs)
    else succF $ lineEndC (incCol pos) cs

-- After a node that ends within a line (a flow collection or quoted
-- scalar) in block context: only white space and a comment may follow
-- on the same line. Stops before the line break.
lineEnd : (sw : Bool) -> Position -> (cs : List Char) -> Result0 False Char cs (BoundedErr YErr) Position
lineEnd sw pos [] = Succ0 pos []
lineEnd sw pos (c :: cs) =
  if isWhite c then succF $ lineEnd True (incCol pos) cs
  else if isBreak c then Succ0 pos (c :: cs)
  else if c == '#' && sw then succF $ lineEndC (incCol pos) cs
  else custom (oneChar pos) TrailingContent

--------------------------------------------------------------------------------
--          Nodes
--------------------------------------------------------------------------------

-- Spec context note: `inFlow` distinguishes the FLOW-IN/FLOW-KEY
-- contexts (inside a flow collection) from FLOW-OUT/BLOCK-* (outside),
-- which changes where plain scalars end. `mi` is the minimum number of
-- indentation spaces for continuation lines (the spec's `n + 1`); `n`
-- is the column at which a block collection's entries are anchored.

mutual
  ||| Continuation lines of a plain scalar [spec: ns-plain-multi-line],
  ||| folded onto the text accumulated so far.
  plainMore :
       (inFlow : Bool)
    -> (mi : Nat)
    -> (acc : String)
    -> (pos : Position)
    -> (cs : List Char)
    -> (0 a : SuffixAcc cs)
    -> Result0 False Char cs (BoundedErr YErr) (String, Position)
  plainMore inFlow mi acc pos cs (SA r) = case plainCont inFlow mi cs of
    Stop => Succ0 (acc, pos) cs
    More k rem prf => case plainSegment inFlow rem of
      Succ s rem2 @{p2} =>
        let acc2 := acc ++ fold k ++ s
            pos2 := move (endPos pos prf) p2
            0 pp := trans p2 prf
         in trans (plainMore inFlow mi acc2 pos2 rem2 (r @{pp})) (weaken pp)
      Fail start errEnd err => Fail0 (boundedErr (endPos pos prf) start errEnd err)

    where
      fold : Nat -> String
      fold 0 = " "
      fold k = replicate k '\n'

  ||| An inline node candidate: a single-line plain scalar or a flow
  ||| collection, parsed into its own event buffer so callers can
  ||| detect implicit mapping keys.
  cand :
       (inFlow : Bool)
    -> (mi : Nat)
    -> (pos : Position)
    -> (cs : List Char)
    -> (0 a : SuffixAcc cs)
    -> Result0 True Char cs (BoundedErr YErr) (Pending, Position)
  cand inFlow mi pos [] _ = eoi
  cand inFlow mi pos (c :: cs) sa =
    if c == '[' || c == '{'
      then case flowNode inFlow mi (YS pos [<]) (c :: cs) sa of
        Fail0 e => Fail0 e
        Succ0 st1 r1 => Succ0 (PFlow st1.evs, st1.pos) r1
      else if isPlainFirst inFlow c cs
        then case plainSegment inFlow (c :: cs) of
          Succ s rem @{prf}     => Succ0 (PScalar s, move pos prf) rem
          Fail start errEnd err => Fail0 (boundedErr pos start errEnd err)
        else parseFail (oneChar pos) (Unknown $ pack [c])

  ||| A single flow node [spec: ns-flow-node]: a plain scalar (with
  ||| line folding) or a flow collection. Expects the input to be at a
  ||| content character.
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
            case plainMore inFlow mi s (move st.pos prf) rem (r @{prf}) of
              Fail0 e => Fail0 e
              Succ0 (s2, p2) rem2 @{q2} =>
                Succ0 (YS p2 (st.evs :< Scalar Nothing NoTag Plain s2)) rem2
                  @{trans q2 prf}
          Fail start errEnd err => Fail0 (boundedErr st.pos start errEnd err)
        else parseFail (oneChar st.pos) (Unknown $ pack [c])

  ||| Inside a flow sequence [spec: c-flow-sequence], at a content
  ||| character: an entry (possibly a single `key: value` pair) or the
  ||| closing bracket.
  flowSeq : (mi : Nat) -> (b : Bounds) -> Rule True YState
  flowSeq mi b st (']' :: cs) _ = Succ0 (emit SeqEnd $ {pos $= incCol} st) cs
  flowSeq mi b st []          _ = unclosed b "["
  flowSeq mi b st cs sa@(SA r) =
    case cand True mi st.pos cs sa of
      Fail0 e => Fail0 e
      Succ0 (pend, p1) r1 @{q1} =>
        let IL cnt r2 w := inlineWhite r1
            p2   := addCol cnt p1
            0 pw := trans w q1
         in if colonFlow r2
              then -- a single pair, an implicit mapping [spec: ns-flow-pair]
                if p1.line /= st.pos.line
                  then custom (BS st.pos p1) InvalidKey
                  else case r2 of
                    ':' :: r3 =>
                      let evs1 := flushPend (st.evs :< MapStart True Nothing NoTag) pend
                          0 pc := trans (uncons Same) (trans w q1)
                       in case flowSkip "[" b mi False (incCol p2) r3 of
                            Fail0 e => Fail0 e
                            Succ0 p4 r4 @{q4} =>
                              let 0 p4c := trans q4 pc
                               in case flowVal mi (YS p4 evs1) r4 (r @{p4c}) of
                                    Fail0 e => Fail0 e
                                    Succ0 st5 r5 @{q5} =>
                                      let 0 p5c := trans q5 p4c
                                       in succT (seqTail mi b (emit MapEnd st5) r5 (r @{p5c})) @{p5c}
                    _ => unclosed b "["
              else case pend of
                PFlow d   =>
                  succT (seqTail mi b (YS p2 (st.evs ++ d)) r2 (r @{pw})) @{pw}
                PScalar s =>
                  case plainMore True mi s p2 r2 (r @{pw}) of
                    Fail0 e => Fail0 e
                    Succ0 (s2, p3) r3 @{q3} =>
                      let 0 pp := trans q3 pw
                          st3  := YS p3 (st.evs :< Scalar Nothing NoTag Plain s2)
                       in succT (seqTail mi b st3 r3 (r @{pp})) @{pp}

  ||| After a flow sequence entry: a comma and further entries, or the
  ||| closing bracket.
  seqTail : (mi : Nat) -> (b : Bounds) -> Rule True YState
  seqTail mi b st cs (SA r) = case flowSkip "[" b mi False st.pos cs of
    Fail0 e => Fail0 e
    Succ0 p2 (']' :: r2) @{q2} =>
      Succ0 (YS (incCol p2) (st.evs :< SeqEnd)) r2 @{trans (uncons Same) q2}
    Succ0 p2 (',' :: r2) @{q2} =>
      case flowSkip "[" b mi False (incCol p2) r2 of
        Fail0 e => Fail0 e
        Succ0 p3 r3 @{q3} =>
          let 0 pp := trans q3 (trans (uncons Same) q2)
           in succT (flowSeq mi b (YS p3 st.evs) r3 (r @{pp})) @{pp}
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

  ||| The value of a flow mapping entry or pair, after its `:`
  ||| indicator and any separation: empty if the entry ends here.
  flowVal : (mi : Nat) -> Rule False YState
  flowVal mi st []          _   = Succ0 ({evs $= emptyScalar} st) []
  flowVal mi st (',' :: cs) _   = Succ0 ({evs $= emptyScalar} st) (',' :: cs)
  flowVal mi st ('}' :: cs) _   = Succ0 ({evs $= emptyScalar} st) ('}' :: cs)
  flowVal mi st (']' :: cs) _   = Succ0 ({evs $= emptyScalar} st) (']' :: cs)
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

  ||| A block node [spec: s-l+block-node]: input at a content
  ||| character, whose column defines the node's indentation.
  blockNode : (mi : Nat) -> Rule True YState
  blockNode mi st [] _ = eoi
  blockNode mi st (c :: cs) sa@(SA r) =
    let n := st.pos.col
     in if c == '-' && wordEnd cs
          then seqLoop n (emit (SeqStart False Nothing NoTag) st) (c :: cs) sa
        else if c == '?' && wordEnd cs
          then case expEntry n (emit (MapStart False Nothing NoTag) st) (c :: cs) sa of
            Fail0 e => Fail0 e
            Succ0 st1 r1 @{q1} => trans (blockMap n st1 r1 (r @{q1})) q1
        else if c == ':' && wordEnd cs
          then
            let evs1 := emptyScalar (st.evs :< MapStart False Nothing NoTag)
             in case afterKey n (YS (incCol st.pos) evs1) cs (r @{uncons Same}) of
                  Fail0 e => Fail0 e
                  Succ0 st1 r1 @{q1} =>
                    let 0 p1 := trans q1 (uncons Same)
                     in trans (blockMap n st1 r1 (r @{p1})) p1
        else case cand False mi st.pos (c :: cs) sa of
          Fail0 e => Fail0 e
          Succ0 (pend, p1) r1 @{q1} =>
            let IL cnt r2 w := inlineWhite r1
                p2   := addCol cnt p1
                0 pw := trans w q1
             in if colonBlock r2
                  then -- this node is a block mapping; `pend` its first key
                    if p1.line /= st.pos.line
                      then custom (BS st.pos p1) InvalidKey
                      else case r2 of
                        ':' :: r3 =>
                          let evs1 := flushPend (st.evs :< MapStart False Nothing NoTag) pend
                              0 pc := trans (uncons Same) (trans w q1)
                           in case afterKey n (YS (incCol p2) evs1) r3 (r @{pc}) of
                                Fail0 e => Fail0 e
                                Succ0 st4 r4 @{q4} =>
                                  let 0 p4 := trans q4 pc
                                   in trans (blockMap n st4 r4 (r @{p4})) p4
                        _ => eoi
                  else case pend of
                    PFlow d => case lineEnd (cnt > 0) p2 r2 of
                      Fail0 e => Fail0 e
                      Succ0 p3 r3 @{q3} =>
                        Succ0 (YS p3 (st.evs ++ d)) r3 @{trans q3 pw}
                    PScalar s => case plainMore False mi s p2 r2 (r @{pw}) of
                      Fail0 e => Fail0 e
                      Succ0 (s2, p3) r3 @{q3} =>
                        if colonBlock r3
                          then custom (BS st.pos p3) InvalidKey
                          else
                            Succ0 (YS p3 (st.evs :< Scalar Nothing NoTag Plain s2)) r3
                              @{trans q3 pw}

  ||| Entries of a block sequence anchored at column `n` [spec:
  ||| l+block-sequence], starting at a `- ` indicator. Emits the SeqEnd
  ||| when the indentation ends.
  seqLoop : (n : Nat) -> Rule True YState
  seqLoop n st ('-' :: cs) (SA r) =
    case seqEntry n (YS (incCol st.pos) st.evs) cs (r @{uncons Same}) of
      Fail0 e => Fail0 e
      Succ0 st1 r1 @{q1} =>
        let 0 p1 := trans q1 (uncons Same)
         in case skipToContent r1 of
              SR (L ind LContent) r2 prf2 =>
                if ind == n && dashNext r2
                  then
                    let 0 pp := trans prf2 p1
                     in succT (seqLoop n (YS (endPos st1.pos prf2) st1.evs) r2 (r @{pp})) @{pp}
                  else Succ0 (emit SeqEnd st1) r1 @{p1}
              SR _ _ _ => Succ0 (emit SeqEnd st1) r1 @{p1}
  seqLoop n st (x :: _) _ = parseFail (oneChar st.pos) (Expected ["'-'"] (pack [x]))
  seqLoop n st []       _ = eoi

  ||| A block sequence entry after its `- ` indicator [spec:
  ||| c-l-block-seq-entry]: same-line content (including compact
  ||| collections), a more indented node on following lines, or empty.
  seqEntry : (n : Nat) -> Rule False YState
  seqEntry n st cs sa@(SA r) =
    let IL cnt r2 w := inlineWhite cs
        p2 := addCol cnt st.pos
     in case r2 of
          [] => Succ0 (YS p2 (emptyScalar st.evs)) [] @{w}
          x :: xs =>
            if isBreak x || x == '#'
              then case skipToContent (x :: xs) of
                SR (L ind LContent) r3 prf3 =>
                  if ind >= S n
                    then
                      let st3 := YS (endPos p2 prf3) st.evs
                       in case trans prf3 w of
                            Same     => weaken $ blockNode (S n) st3 r3 sa
                            Uncons u =>
                              weaken $ trans (blockNode (S n) st3 r3 (r @{uncons u}))
                                             (weaken (uncons u))
                    else Succ0 (YS p2 (emptyScalar st.evs)) (x :: xs) @{w}
                SR _ _ _ => Succ0 (YS p2 (emptyScalar st.evs)) (x :: xs) @{w}
              else
                let st2 := YS p2 st.evs
                 in case w of
                      Same     => weaken $ blockNode (S n) st2 (x :: xs) sa
                      Uncons u =>
                        weaken $ trans (blockNode (S n) st2 (x :: xs) (r @{uncons u}))
                                       (weaken (uncons u))

  ||| Further entries of a block mapping anchored at column `n` [spec:
  ||| l+block-mapping]: emits the MapEnd when the indentation ends.
  blockMap : (n : Nat) -> Rule False YState
  blockMap n st cs sa@(SA r) = case skipToContent cs of
    SR (L ind LContent) r2 prf2 =>
      if ind == n
        then
          let st2 := YS (endPos st.pos prf2) st.evs
           in case prf2 of
                Same => case mapEntry n st2 r2 sa of
                  Fail0 e => Fail0 e
                  Succ0 st3 r3 @{q3} =>
                    trans (blockMap n st3 r3 (r @{q3})) (weaken q3)
                Uncons u => case mapEntry n st2 r2 (r @{uncons u}) of
                  Fail0 e => Fail0 e
                  Succ0 st3 r3 @{q3} =>
                    let 0 p3 := trans q3 (uncons u)
                     in trans (blockMap n st3 r3 (r @{p3})) (weaken p3)
        else Succ0 (emit MapEnd st) cs
    SR _ _ _ => Succ0 (emit MapEnd st) cs

  ||| A single block mapping entry at indent `n` [spec:
  ||| ns-l-block-map-entry]: explicit (`? `), an empty key (`: `), or
  ||| an implicit single-line key followed by `:`.
  mapEntry : (n : Nat) -> Rule True YState
  mapEntry n st [] _ = eoi
  mapEntry n st (c :: cs) sa@(SA r) =
    if c == '?' && wordEnd cs
      then expEntry n st (c :: cs) sa
    else if c == ':' && wordEnd cs
      then case afterKey n (YS (incCol st.pos) (emptyScalar st.evs)) cs (r @{uncons Same}) of
        Fail0 e => Fail0 e
        Succ0 st1 r1 @{q1} => Succ0 st1 r1 @{trans q1 (uncons Same)}
    else case cand False (S n) st.pos (c :: cs) sa of
      Fail0 e => Fail0 e
      Succ0 (pend, p1) r1 @{q1} =>
        let IL cnt r2 w := inlineWhite r1
            p2   := addCol cnt p1
            0 pw := trans w q1
         in if colonBlock r2
              then
                if p1.line /= st.pos.line
                  then custom (BS st.pos p1) InvalidKey
                  else case r2 of
                    ':' :: r3 =>
                      let 0 pc := trans (uncons Same) (trans w q1)
                       in case afterKey n (YS (incCol p2) (flushPend st.evs pend)) r3 (r @{pc}) of
                            Fail0 e => Fail0 e
                            Succ0 st4 r4 @{q4} => Succ0 st4 r4 @{trans q4 pc}
                    _ => eoi
              else case r2 of
                x :: _ => parseFail (oneChar p2) (Expected ["':'"] (pack [x]))
                []     => eoi

  ||| An explicit block mapping entry [spec:
  ||| c-l-block-map-explicit-entry], starting at its `?` indicator at
  ||| indent `n`: a block node as key, then optionally a `:` line at
  ||| the same indent with the value.
  expEntry : (n : Nat) -> Rule True YState
  expEntry n st ('?' :: cs) sa@(SA r) =
    let IL cnt r2 w := inlineWhite cs
        p2 := addCol cnt (incCol st.pos)
        keyRes : Result0 True Char ('?' :: cs) (BoundedErr YErr) YState :=
          case r2 of
            [] => Succ0 (YS p2 (emptyScalar st.evs)) [] @{trans w (uncons Same)}
            x :: xs =>
              if isBreak x || x == '#'
                then case skipToContent (x :: xs) of
                  SR (L ind LContent) r3 prf3 =>
                    if ind >= S n
                      then
                        let 0 p3 := trans prf3 (trans w (uncons Same))
                         in succT (blockNode (S n) (YS (endPos p2 prf3) st.evs) r3 (r @{p3})) @{p3}
                      else Succ0 (YS p2 (emptyScalar st.evs)) (x :: xs) @{trans w (uncons Same)}
                  SR _ _ _ => Succ0 (YS p2 (emptyScalar st.evs)) (x :: xs) @{trans w (uncons Same)}
                else
                  let 0 pw := trans w (uncons Same)
                   in succT (blockNode (S n) (YS p2 st.evs) (x :: xs) (r @{pw})) @{pw}
     in case keyRes of
          Fail0 e => Fail0 e
          Succ0 stK remK @{qK} => case skipToContent remK of
            SR (L ind LContent) rV prfV =>
              if ind == n && colonBlock rV
                then case rV of
                  ':' :: rV2 =>
                    let pV   := incCol (endPos stK.pos prfV)
                        0 pc := trans (uncons Same) (trans prfV qK)
                     in case afterKey n (YS pV stK.evs) rV2 (r @{pc}) of
                          Fail0 e => Fail0 e
                          Succ0 stF rF @{qF} => Succ0 stF rF @{trans qF pc}
                  _ => eoi
                else Succ0 ({evs $= emptyScalar} stK) remK @{qK}
            SR _ _ _ => Succ0 ({evs $= emptyScalar} stK) remK @{qK}
  expEntry n st (x :: _) _ = parseFail (oneChar st.pos) (Expected ["'?'"] (pack [x]))
  expEntry n st []       _ = eoi

  ||| The value of a block mapping entry, after its `:` indicator
  ||| [spec: c-l-block-map-implicit-value]: an inline value on the same
  ||| line, a block node on following lines, a sequence at the same
  ||| indent (the "seq-spaces" exception), or empty.
  afterKey : (n : Nat) -> Rule False YState
  afterKey n st cs sa@(SA r) =
    let IL cnt r2 w := inlineWhite cs
        p2 := addCol cnt st.pos
     in case r2 of
          [] => Succ0 (YS p2 (emptyScalar st.evs)) [] @{w}
          x :: xs =>
            if isBreak x || x == '#'
              then case skipToContent (x :: xs) of
                SR (L ind LContent) r3 prf3 =>
                  let st3 := YS (endPos p2 prf3) st.evs
                   in if ind >= S n
                        then case trans prf3 w of
                          Same     => weaken $ blockNode (S n) st3 r3 sa
                          Uncons u =>
                            weaken $ trans (blockNode (S n) st3 r3 (r @{uncons u}))
                                           (weaken (uncons u))
                        else if ind == n && dashNext r3
                          then
                            let st3s := emit (SeqStart False Nothing NoTag) st3
                             in case trans prf3 w of
                                  Same     => weaken $ seqLoop n st3s r3 sa
                                  Uncons u =>
                                    weaken $ trans (seqLoop n st3s r3 (r @{uncons u}))
                                                   (weaken (uncons u))
                          else Succ0 (YS p2 (emptyScalar st.evs)) (x :: xs) @{w}
                SR _ _ _ => Succ0 (YS p2 (emptyScalar st.evs)) (x :: xs) @{w}
              else case w of
                Same     => weaken $ inlineVal n (YS p2 st.evs) (x :: xs) sa
                Uncons u =>
                  weaken $ trans (inlineVal n (YS p2 st.evs) (x :: xs) (r @{uncons u}))
                                 (weaken (uncons u))

  ||| A mapping value on the same line as its `:` indicator: a flow
  ||| node [spec: s-l+flow-in-block].
  inlineVal : (n : Nat) -> Rule True YState
  inlineVal n st [] _ = eoi
  inlineVal n st (c :: cs) sa@(SA r) =
    if c == '[' || c == '{'
      then case flowNode False (S n) st (c :: cs) sa of
        Fail0 e => Fail0 e
        Succ0 st1 r1 @{q1} => case lineEnd False st1.pos r1 of
          Fail0 e => Fail0 e
          Succ0 p2 r2 @{q2} => Succ0 (YS p2 st1.evs) r2 @{trans q2 q1}
      else if isPlainFirst False c cs
        then case plainSegment False (c :: cs) of
          Succ s rem @{prf} =>
            case plainMore False (S n) s (move st.pos prf) rem (r @{prf}) of
              Fail0 e => Fail0 e
              Succ0 (s2, p2) r2 @{q2} =>
                if colonBlock r2
                  then custom (BS st.pos p2) InvalidKey
                  else
                    Succ0 (YS p2 (st.evs :< Scalar Nothing NoTag Plain s2)) r2
                      @{trans q2 prf}
          Fail start errEnd err => Fail0 (boundedErr st.pos start errEnd err)
        else parseFail (oneChar st.pos) (Unknown $ pack [c])

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
    content st1 rem acc = case blockNode 0 st1 rem acc of
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
