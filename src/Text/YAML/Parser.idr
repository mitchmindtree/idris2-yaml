module Text.YAML.Parser

import Data.Maybe
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

||| An empty node with the given properties [spec: e-scalar].
%inline
emptyScalarP : Props -> SnocList Event -> SnocList Event
emptyScalarP pr = (:< Scalar pr.anchor pr.tag Plain "")

%inline
emptyScalar : SnocList Event -> SnocList Event
emptyScalar = emptyScalarP noProps

||| An inline node candidate for implicit-key detection: a single-line
||| scalar (its event not yet emitted, since a plain scalar might yet
||| grow by line folding), an alias, node properties not followed by
||| inline content, or a flow collection parsed into its own event
||| buffer.
data Pending : Type where
  PScalar : Props -> Style -> String -> Pending
  PAlias  : Anchor -> Pending
  PProps  : Props -> Pending
  PFlow   : SnocList Event -> Pending

flushPend : SnocList Event -> Pending -> SnocList Event
flushPend evs (PScalar pr sty s) = evs :< Scalar pr.anchor pr.tag sty s
flushPend evs (PAlias a)         = evs :< Alias a
flushPend evs (PProps pr)        = evs :< Scalar pr.anchor pr.tag Plain ""
flushPend evs (PFlow d)          = evs ++ d

||| Attaches properties from a preceding line to a flow collection's
||| opening event.
patchFlow : Props -> SnocList Event -> Either YErr (SnocList Event)
patchFlow pr evs = case evs <>> [] of
  SeqStart f a t :: es =>
    (\p => [<] <>< (SeqStart f p.anchor p.tag :: es)) <$> mergeProps pr (MkProps a t)
  MapStart f a t :: es =>
    (\p => [<] <>< (MapStart f p.anchor p.tag :: es)) <$> mergeProps pr (MkProps a t)
  _ => Right evs

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

-- Can an inline node candidate start here?
candStart : (inFlow : Bool) -> List Char -> Bool
candStart inFlow (c :: cs) =
  c == '[' || c == '{' || c == '\'' || c == '"' || c == '*' ||
  isPlainFirst inFlow c cs
candStart _ [] = False

-- Does a block scalar start here? Returns whether it is folded.
bsStart : List Char -> Maybe Bool
bsStart ('|' :: _) = Just False
bsStart ('>' :: _) = Just True
bsStart _          = Nothing

breakStart : List Char -> Bool
breakStart (c :: _) = isBreak c || c == '#'
breakStart []       = False

propStart : List Char -> Bool
propStart (c :: _) = c == '&' || c == '!'
propStart []       = False

colonNext : List Char -> Bool
colonNext (':' :: _) = True
colonNext _          = False

-- Does this line hold only node properties (and perhaps a comment)?
propsOnlyLine : List Char -> Bool
propsOnlyLine = go
  where
    mutual
      tok : List Char -> Bool
      tok (c :: cs) =
        if isWhite c || isBreak c then go (c :: cs) else tok cs
      tok [] = True

      go : List Char -> Bool
      go (' '  :: cs) = go cs
      go ('\t' :: cs) = go cs
      go ('\n' :: _)  = True
      go ('#'  :: _)  = True
      go ('&'  :: cs) = tok cs
      go ('!'  :: cs) = tok cs
      go []           = True
      go _            = False

-- JSON-like nodes allow an adjacent `:` value indicator
-- [spec: c-ns-flow-map-json-key-entry].
jsonLike : Pending -> Bool
jsonLike (PScalar _ SingleQ _) = True
jsonLike (PScalar _ DoubleQ _) = True
jsonLike (PFlow _)             = True
jsonLike _                     = False

-- Does the candidate carry node properties?
pendProps : Pending -> Bool
pendProps (PScalar pr _ _) = not (isNoProps pr)
pendProps (PProps _)       = True
pendProps _                = False

--------------------------------------------------------------------------------
--          Rule Type
--------------------------------------------------------------------------------

||| A parsing rule, consuming a prefix of the remaining input (a strict
||| one if `b` is `True`).
|||
||| Totality: all recursion in the rules below runs over the strictly
||| shrinking character list via `SuffixAcc`. Since some nodes may be
||| empty (consuming nothing), every loop derives its strictness from a
||| separator it consumed itself (a comma, colon, dash, marker, or line
||| break) before recursing. Lookahead over blank and comment lines
||| (`skipToContent`) returns a non-erased, possibly-empty `Suffix`:
||| where a rule continues after such a skip without other consumption,
||| it matches `Same`/`Uncons` explicitly so the recursion goes through
||| a projection of its `SuffixAcc` argument.
public export
0 Rule : Bool -> Type -> Type
Rule b a =
     YState
  -> (cs : List Char)
  -> (0 acc : SuffixAcc cs)
  -> Result0 b Char cs (BoundedErr YErr) a

--------------------------------------------------------------------------------
--          Node Properties
--------------------------------------------------------------------------------

||| Parses node properties [spec: c-ns-properties]: an anchor and a tag
||| in either order, separated by white space within the line. Must be
||| called at a `&` or `!`.
pProps :
     TagEnv
  -> Props
  -> Position
  -> (cs : List Char)
  -> (0 a : SuffixAcc cs)
  -> Result0 True Char cs (BoundedErr YErr) (Props, Position)
pProps env pr pos ('&' :: cs) sa@(SA r) = case pr.anchor of
  Just _  => custom (oneChar pos) MultipleAnchors
  Nothing => case anchorName ('&' :: cs) of
    Succ nm rem @{prf} =>
      let IL cnt tbw2 rem2 w := inlineWhite rem
          pos2 := addCol cnt (move pos prf)
          pr2  := {anchor := Just nm} pr
          0 pp := trans w prf
       in if propStart rem2
            then succT (pProps env pr2 pos2 rem2 (r @{pp})) @{pp}
            else Succ0 (pr2, pos2) rem2 @{pp}
    Fail start errEnd err => Fail0 (boundedErr pos start errEnd err)
pProps env pr pos ('!' :: cs) sa@(SA r) = case pr.tag of
  NoTag => case tagToken ('!' :: cs) of
    Succ et rem @{prf} =>
      let pos1 := move pos prf
       in case resolved et of
            Left e   => custom (BS pos pos1) e
            Right tg =>
              let IL cnt tbw2 rem2 w := inlineWhite rem
                  pr2  := {tag := tg} pr
                  0 pp := trans w prf
               in if propStart rem2
                    then succT (pProps env pr2 (addCol cnt pos1) rem2 (r @{pp})) @{pp}
                    else Succ0 (pr2, addCol cnt pos1) rem2 @{pp}
    Fail start errEnd err => Fail0 (boundedErr pos start errEnd err)
  _ => custom (oneChar pos) MultipleTags

  where
    resolved : Either Tag (String, String) -> Either YErr Tag
    resolved (Left t)       = Right t
    resolved (Right (h, s)) = resolveTag env h s
pProps env pr pos [] _ = eoi
pProps env pr pos (c :: cs) _ =
  parseFail (oneChar pos) (Expected ["'&'", "'!'"] (pack [c]))

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
  SR (L _ LEnd _) rem prf => Succ0 (endPos pos prf) rem @{prf}
  SR (L ind LContent tb) rem prf =>
    if ind >= mi
      then Succ0 (endPos pos prf) rem @{prf}
      else custom (oneChar $ endPos pos prf) BadIndent
  SR (L _ _ _) rem prf => unclosed b tok

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

-- After a node that ends within a line (a flow collection, quoted
-- scalar or alias) in block context: only white space and a comment
-- may follow on the same line. Stops before the line break.
lineEnd : (sw : Bool) -> Position -> (cs : List Char) -> Result0 False Char cs (BoundedErr YErr) Position
lineEnd sw pos [] = Succ0 pos []
lineEnd sw pos (c :: cs) =
  if isWhite c then succF $ lineEnd True (incCol pos) cs
  else if isBreak c then Succ0 pos (c :: cs)
  else if c == '#' && sw then succF $ lineEndC (incCol pos) cs
  else custom (oneChar pos) TrailingContent

--------------------------------------------------------------------------------
--          Directives
--------------------------------------------------------------------------------

||| Interprets a directive line [spec: l-directive]: `%YAML` (at most
||| once per document, major version 1), `%TAG` (no duplicate handles),
||| anything else is reserved and ignored.
parseDirective : TagEnv -> (sawYaml : Bool) -> String -> Either YErr (TagEnv, Bool)
parseDirective env sy ln = case takeWhile (not . isPrefixOf "#") (words ln) of
  ["%YAML", v]     =>
    if sy then Left (BadDirective "duplicate %YAML directive")
    else if versionOk (unpack v) then Right (env, True)
    else Left (BadVersion v)
  ("%YAML" :: _)   => Left (BadDirective ln)
  ["%TAG", h, pre] => case lookup h env.handles of
    Just _  => Left (DuplicateHandle h)
    Nothing =>
      if handleOk (unpack h)
        then Right (TE ((h, pre) :: env.handles), sy)
        else Left (BadDirective ln)
  ("%TAG" :: _)    => Left (BadDirective ln)
  _                => Right (env, sy)

  where
    versionOk : List Char -> Bool
    versionOk ('1' :: '.' :: ds@(_ :: _)) = all isDigit ds
    versionOk _                           = False

    inner : List Char -> Bool
    inner ['!']     = True
    inner (c :: t)  = isWordChar c && inner t
    inner []        = False

    handleOk : List Char -> Bool
    handleOk ['!']      = True
    handleOk ('!' :: t) = inner t
    handleOk _          = False

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

  ||| An inline node candidate: properties, an alias, a single-line
  ||| scalar or a flow collection, parsed into its own event buffer so
  ||| callers can detect implicit mapping keys.
  cand :
       (inFlow : Bool)
    -> (mi : Nat)
    -> TagEnv
    -> Props
    -> Position
    -> (cs : List Char)
    -> (0 a : SuffixAcc cs)
    -> Result0 True Char cs (BoundedErr YErr) (Pending, Position)
  cand inFlow mi env pr pos [] _ = eoi
  cand inFlow mi env pr pos (c :: cs) sa@(SA r) =
    if c == '&' || c == '!'
      then case pProps env pr pos (c :: cs) sa of
        Fail0 e => Fail0 e
        Succ0 (pr2, p1) r1 @{q1} =>
          if candStart inFlow r1
            then succT (cand inFlow mi env pr2 p1 r1 (r @{q1})) @{q1}
            else Succ0 (PProps pr2, p1) r1 @{q1}
    else if c == '*'
      then
        if isNoProps pr
          then case anchorName (c :: cs) of
            Succ nm rem @{prf}    => Succ0 (PAlias nm, move pos prf) rem
            Fail start errEnd err => Fail0 (boundedErr pos start errEnd err)
          else parseFail (oneChar pos) (Unknown "properties on alias node")
    else if c == '[' || c == '{'
      then case flowNode inFlow mi env pr (YS pos [<]) (c :: cs) sa of
        Fail0 e => Fail0 e
        Succ0 st1 r1 => Succ0 (PFlow st1.evs, st1.pos) r1
    else if c == '\'' || c == '"'
      then
        let (tok, sty) := if c == '"'
                            then (doubleQuoted mi, DoubleQ)
                            else (singleQuoted mi, SingleQ)
         in case tok (c :: cs) of
              Succ s rem @{prf}     => Succ0 (PScalar pr sty s, endPos pos prf) rem
              Fail start errEnd err => Fail0 (boundedErr pos start errEnd err)
    else if isPlainFirst inFlow c cs
      then case plainSegment inFlow (c :: cs) of
        Succ s rem @{prf}     => Succ0 (PScalar pr Plain s, move pos prf) rem
        Fail start errEnd err => Fail0 (boundedErr pos start errEnd err)
      else parseFail (oneChar pos) (Unknown $ pack [c])

  ||| A single flow node [spec: ns-flow-node]: properties, an alias, a
  ||| scalar or a flow collection. Expects the input to be at a content
  ||| character.
  flowNode : (inFlow : Bool) -> (mi : Nat) -> TagEnv -> Props -> Rule True YState
  flowNode inFlow mi env pr st [] _ = eoi
  flowNode inFlow mi env pr st (c :: cs) sa@(SA r) = case c of
    '&' => flowProps inFlow mi env pr st (c :: cs) sa
    '!' => flowProps inFlow mi env pr st (c :: cs) sa
    '*' =>
      if isNoProps pr
        then case anchorName ('*' :: cs) of
          Succ nm rem @{prf} =>
            Succ0 (YS (move st.pos prf) (st.evs :< Alias nm)) rem @{prf}
          Fail start errEnd err => Fail0 (boundedErr st.pos start errEnd err)
        else parseFail (oneChar st.pos) (Unknown "properties on alias node")
    '[' => case flowSkip "[" (oneChar st.pos) mi False (incCol st.pos) cs of
      Fail0 e => Fail0 e
      Succ0 p1 r1 @{q1} =>
        let 0 pp := trans q1 (uncons Same)
            st1  := YS p1 (st.evs :< SeqStart True pr.anchor pr.tag)
         in succT (flowSeq env mi (oneChar st.pos) st1 r1 (r @{pp})) @{pp}
    '{' => case flowSkip "{" (oneChar st.pos) mi False (incCol st.pos) cs of
      Fail0 e => Fail0 e
      Succ0 p1 r1 @{q1} =>
        let 0 pp := trans q1 (uncons Same)
            st1  := YS p1 (st.evs :< MapStart True pr.anchor pr.tag)
         in succT (flowMap env mi (oneChar st.pos) st1 r1 (r @{pp})) @{pp}
    '\'' => case singleQuoted mi (c :: cs) of
      Succ s rem @{prf} =>
        Succ0 (YS (endPos st.pos prf) (st.evs :< Scalar pr.anchor pr.tag SingleQ s)) rem
      Fail start errEnd err => Fail0 (boundedErr st.pos start errEnd err)
    '"' => case doubleQuoted mi (c :: cs) of
      Succ s rem @{prf} =>
        Succ0 (YS (endPos st.pos prf) (st.evs :< Scalar pr.anchor pr.tag DoubleQ s)) rem
      Fail start errEnd err => Fail0 (boundedErr st.pos start errEnd err)
    _   =>
      if isPlainFirst inFlow c cs
        then case plainSegment inFlow (c :: cs) of
          Succ s rem @{prf} =>
            case plainMore inFlow mi s (move st.pos prf) rem (r @{prf}) of
              Fail0 e => Fail0 e
              Succ0 (s2, p2) rem2 @{q2} =>
                Succ0 (YS p2 (st.evs :< Scalar pr.anchor pr.tag Plain s2)) rem2
                  @{trans q2 prf}
          Fail start errEnd err => Fail0 (boundedErr st.pos start errEnd err)
        else parseFail (oneChar st.pos) (Unknown $ pack [c])

  ||| Properties of a flow node, then the node itself, which may sit on
  ||| a following line or be empty.
  flowProps : (inFlow : Bool) -> (mi : Nat) -> TagEnv -> Props -> Rule True YState
  flowProps inFlow mi env pr st cs sa@(SA r) = case pProps env pr st.pos cs sa of
    Fail0 e => Fail0 e
    Succ0 (pr2, p1) r1 @{q1} =>
      if candStart inFlow r1
        then succT (flowNode inFlow mi env pr2 (YS p1 st.evs) r1 (r @{q1})) @{q1}
        else if breakStart r1
          then case skipToContent r1 of
            SR (L ind LContent tb) r2 prf2 =>
              if ind >= mi
                then
                  let 0 pp := trans prf2 q1
                   in succT (flowNode inFlow mi env pr2 (YS (endPos p1 prf2) st.evs) r2 (r @{pp})) @{pp}
                else custom (oneChar $ endPos p1 prf2) BadIndent
            SR _ _ _ => Succ0 (YS p1 (emptyScalarP pr2 st.evs)) r1 @{q1}
          else Succ0 (YS p1 (emptyScalarP pr2 st.evs)) r1 @{q1}

  ||| Inside a flow sequence [spec: c-flow-sequence], at a content
  ||| character: an entry (possibly a `key: value` pair, implicit or
  ||| explicit) or the closing bracket.
  flowSeq : TagEnv -> (mi : Nat) -> (b : Bounds) -> Rule True YState
  flowSeq env mi b st (']' :: cs) _ = Succ0 (emit SeqEnd $ {pos $= incCol} st) cs
  flowSeq env mi b st []          _ = unclosed b "["
  flowSeq env mi b st (':' :: cs) sa@(SA r) =
    -- a pair with an empty key, unless the colon starts a plain scalar
    if plainSafeNext cs
      then seqItem env mi b st (':' :: cs) sa
      else
        let evs1 := emptyScalar (st.evs :< MapStart True Nothing NoTag)
         in case flowSkip "[" b mi False (incCol st.pos) cs of
              Fail0 e => Fail0 e
              Succ0 p1 r1 @{q1} =>
                let 0 pp := trans q1 (uncons Same)
                 in case flowVal env mi (YS p1 evs1) r1 (r @{pp}) of
                      Fail0 e => Fail0 e
                      Succ0 st2 r2 @{q2} =>
                        let 0 p2c := trans q2 pp
                         in succT (seqTail env mi b False (emit MapEnd st2) r2 (r @{p2c})) @{p2c}
  flowSeq env mi b st ('?' :: cs) sa@(SA r) =
    -- an explicit pair [spec: ns-flow-map-explicit-entry]
    if plainSafeNext cs
      then seqItem env mi b st ('?' :: cs) sa
      else
        let evs1 := st.evs :< MapStart True Nothing NoTag
         in case flowSkip "[" b mi False (incCol st.pos) cs of
              Fail0 e => Fail0 e
              Succ0 p1 r1 @{q1} =>
                let 0 pp := trans q1 (uncons Same)
                 in case pairKey env mi b (YS p1 evs1) r1 (r @{pp}) of
                      Fail0 e => Fail0 e
                      Succ0 st2 r2 @{q2} =>
                        let 0 p2c := trans q2 pp
                         in succT (seqTail env mi b False st2 r2 (r @{p2c})) @{p2c}
  flowSeq env mi b st cs sa = seqItem env mi b st cs sa

  ||| The key (or whole content) of an explicit flow pair, after its
  ||| `?` indicator, followed by an optional `: value`; emits the
  ||| closing MapEnd.
  pairKey : TagEnv -> (mi : Nat) -> (b : Bounds) -> Rule False YState
  pairKey env mi b st cs sa@(SA r) =
    if emptyNext cs
      then Succ0 ({evs $= (:< MapEnd) . emptyScalar . emptyScalar} st) cs
      else case flowNode True mi env noProps st cs sa of
        Fail0 e => Fail0 e
        Succ0 st1 r1 @{q1} => case flowSkip "[" b mi False st1.pos r1 of
          Fail0 e => Fail0 e
          Succ0 p2 (':' :: r2) @{q2} =>
            case flowSkip "[" b mi False (incCol p2) r2 of
              Fail0 e => Fail0 e
              Succ0 p3 r3 @{q3} =>
                let 0 pp := trans q3 (trans (uncons Same) (trans q2 q1))
                 in case flowVal env mi (YS p3 st1.evs) r3 (r @{pp}) of
                      Fail0 e => Fail0 e
                      Succ0 st4 r4 @{q4} =>
                        Succ0 (emit MapEnd st4) r4 @{weaken $ trans q4 pp}
          Succ0 p2 r2 @{q2} =>
            Succ0 (YS p2 (st1.evs :< Scalar Nothing NoTag Plain "" :< MapEnd)) r2
              @{weaken $ trans q2 q1}

    where
      emptyNext : List Char -> Bool
      emptyNext (c :: _) = c == ']' || c == ','
      emptyNext []       = False

  ||| An ordinary flow sequence entry: an inline candidate, possibly
  ||| forming an implicit single pair [spec: ns-flow-pair].
  seqItem : TagEnv -> (mi : Nat) -> (b : Bounds) -> Rule True YState
  seqItem env mi b st cs sa@(SA r) =
    case cand True mi env noProps st.pos cs sa of
      Fail0 e => Fail0 e
      Succ0 (pend, p1) r1 @{q1} =>
        let IL cnt tbw r2 w := inlineWhite r1
            p2   := addCol cnt p1
            0 pw := trans w q1
         in if colonFlow r2 || (jsonLike pend && colonNext r2)
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
                               in case flowVal env mi (YS p4 evs1) r4 (r @{p4c}) of
                                    Fail0 e => Fail0 e
                                    Succ0 st5 r5 @{q5} =>
                                      let 0 p5c := trans q5 p4c
                                       in succT (seqTail env mi b False (emit MapEnd st5) r5 (r @{p5c})) @{p5c}
                    _ => unclosed b "["
              else case pend of
                PFlow d   =>
                  succT (seqTail env mi b (cnt > 0) (YS p2 (st.evs ++ d)) r2 (r @{pw})) @{pw}
                PAlias a  =>
                  succT (seqTail env mi b (cnt > 0) (YS p2 (st.evs :< Alias a)) r2 (r @{pw})) @{pw}
                PProps pr =>
                  succT (seqTail env mi b (cnt > 0) (YS p2 (emptyScalarP pr st.evs)) r2 (r @{pw})) @{pw}
                PScalar pr Plain s =>
                  case plainMore True mi s p2 r2 (r @{pw}) of
                    Fail0 e => Fail0 e
                    Succ0 (s2, p3) r3 @{q3} =>
                      let 0 pp := trans q3 pw
                          st3  := YS p3 (st.evs :< Scalar pr.anchor pr.tag Plain s2)
                       in succT (seqTail env mi b (cnt > 0) st3 r3 (r @{pp})) @{pp}
                PScalar pr sty s =>
                  let st2 := YS p2 (st.evs :< Scalar pr.anchor pr.tag sty s)
                   in succT (seqTail env mi b (cnt > 0) st2 r2 (r @{pw})) @{pw}

  ||| After a flow sequence entry: a comma and further entries, or the
  ||| closing bracket.
  seqTail : TagEnv -> (mi : Nat) -> (b : Bounds) -> (sw : Bool) -> Rule True YState
  seqTail env mi b sw st cs (SA r) = case flowSkip "[" b mi sw st.pos cs of
    Fail0 e => Fail0 e
    Succ0 p2 (']' :: r2) @{q2} =>
      Succ0 (YS (incCol p2) (st.evs :< SeqEnd)) r2 @{trans (uncons Same) q2}
    Succ0 p2 (',' :: r2) @{q2} =>
      case flowSkip "[" b mi False (incCol p2) r2 of
        Fail0 e => Fail0 e
        Succ0 p3 r3 @{q3} =>
          let 0 pp := trans q3 (trans (uncons Same) q2)
           in succT (flowSeq env mi b (YS p3 st.evs) r3 (r @{pp})) @{pp}
    Succ0 p2 [] => unclosed b "["
    Succ0 p2 (x :: _) =>
      parseFail (oneChar p2) (Expected ["','", "']'"] (pack [x]))

  ||| Inside a flow mapping [spec: c-flow-mapping], at a content
  ||| character: an entry or the closing brace.
  flowMap : TagEnv -> (mi : Nat) -> (b : Bounds) -> Rule True YState
  flowMap env mi b st ('}' :: cs) _ = Succ0 (emit MapEnd $ {pos $= incCol} st) cs
  flowMap env mi b st []          _ = unclosed b "{"
  flowMap env mi b st ('?' :: cs) sa@(SA r) =
    -- an explicit entry [spec: ns-flow-map-explicit-entry], unless the
    -- question mark starts a plain scalar
    if plainSafeNext cs
      then flowEntry env mi b st ('?' :: cs) sa
      else case flowSkip "{" b mi False (incCol st.pos) cs of
        Fail0 e => Fail0 e
        Succ0 p1 r1 @{q1} =>
          let 0 pp := trans q1 (uncons Same)
           in if emptyNext r1
                then succT (mapTail env mi b (YS p1 ({evs $= emptyScalar . emptyScalar} st).evs) r1 (r @{pp})) @{pp}
                else succT (flowEntry env mi b (YS p1 st.evs) r1 (r @{pp})) @{pp}

    where
      emptyNext : List Char -> Bool
      emptyNext (c2 :: _) = c2 == '}' || c2 == ','
      emptyNext []        = False

  flowMap env mi b st cs sa = flowEntry env mi b st cs sa

  ||| A single flow mapping entry (without a leading `?` indicator).
  flowEntry : TagEnv -> (mi : Nat) -> (b : Bounds) -> Rule True YState
  flowEntry env mi b st [] _ = unclosed b "{"
  flowEntry env mi b st (c :: cs) sa@(SA r) =
    if c == ':' && not (plainSafeNext cs)
      then -- an entry with an empty key [spec: c-ns-flow-map-empty-key-entry]
        case flowSkip "{" b mi False (incCol st.pos) cs of
          Fail0 e => Fail0 e
          Succ0 p1 r1 @{q1} =>
            let 0 pp := trans q1 (uncons Same)
             in case flowVal env mi (YS p1 (emptyScalar st.evs)) r1 (r @{pp}) of
                  Fail0 e => Fail0 e
                  Succ0 st2 r2 @{q2} => case flowSkip "{" b mi False st2.pos r2 of
                    Fail0 e => Fail0 e
                    Succ0 p3 r3 @{q3} =>
                      let 0 pp3 := trans (trans q3 (trans q2 q1)) (uncons Same)
                       in succT (mapTail env mi b (YS p3 st2.evs) r3 (r @{pp3})) @{pp3}
      else -- an entry starting with a key node
        case flowNode True mi env noProps st (c :: cs) sa of
          Fail0 e => Fail0 e
          Succ0 st1 r1 @{q1} => case flowSkip "{" b mi False st1.pos r1 of
            Fail0 e => Fail0 e
            Succ0 p2 (':' :: r2) @{q2} =>
              case flowSkip "{" b mi False (incCol p2) r2 of
                Fail0 e => Fail0 e
                Succ0 p3 r3 @{q3} =>
                  let 0 pp := trans q3 (trans (uncons Same) (trans q2 q1))
                   in case flowVal env mi (YS p3 st1.evs) r3 (r @{pp}) of
                        Fail0 e => Fail0 e
                        Succ0 st4 r4 @{q4} =>
                          case flowSkip "{" b mi False st4.pos r4 of
                            Fail0 e => Fail0 e
                            Succ0 p5 r5 @{q5} =>
                              let 0 pp5 := trans q5 (trans q4 pp)
                               in succT (mapTail env mi b (YS p5 st4.evs) r5 (r @{pp5})) @{pp5}
            Succ0 p2 r2 @{q2} =>
              -- no colon: the value is empty [spec: ns-flow-map-yaml-key-entry]
              let 0 pp := trans q2 q1
               in succT (mapTail env mi b (YS p2 (emptyScalar st1.evs)) r2 (r @{pp})) @{pp}

  ||| The value of a flow mapping entry or pair, after its `:`
  ||| indicator and any separation: empty if the entry ends here.
  flowVal : TagEnv -> (mi : Nat) -> Rule False YState
  flowVal env mi st []          _   = Succ0 ({evs $= emptyScalar} st) []
  flowVal env mi st (',' :: cs) _   = Succ0 ({evs $= emptyScalar} st) (',' :: cs)
  flowVal env mi st ('}' :: cs) _   = Succ0 ({evs $= emptyScalar} st) ('}' :: cs)
  flowVal env mi st (']' :: cs) _   = Succ0 ({evs $= emptyScalar} st) (']' :: cs)
  flowVal env mi st cs          acc = weaken $ flowNode True mi env noProps st cs acc

  ||| After a complete flow mapping entry: a comma followed by the next
  ||| entry, or the closing brace.
  mapTail : TagEnv -> (mi : Nat) -> (b : Bounds) -> Rule True YState
  mapTail env mi b st ('}' :: cs) _ = Succ0 (emit MapEnd $ {pos $= incCol} st) cs
  mapTail env mi b st (',' :: cs) (SA r) =
    case flowSkip "{" b mi False (incCol st.pos) cs of
      Fail0 e => Fail0 e
      Succ0 p1 r1 @{q1} =>
        let 0 pp := trans q1 (uncons Same)
         in succT (flowMap env mi b (YS p1 st.evs) r1 (r @{pp})) @{pp}
  mapTail env mi b st []          _ = unclosed b "{"
  mapTail env mi b st (x :: _)    _ =
    parseFail (oneChar st.pos) (Expected ["','", "'}'"] (pack [x]))

  ||| A block node [spec: s-l+block-node]: input at a content
  ||| character, whose column defines the node's indentation (unless
  ||| overridden by `nOv`, as for nodes on a `---` marker's line).
  ||| `oprops` are properties from a preceding line, belonging to a
  ||| block collection found here (or merged into a scalar). With
  ||| `tabSep`, the content was preceded by tabs, which is an error for
  ||| block structure [spec 6.1].
  blockNode : (mi : Nat) -> (nOv : Maybe Nat) -> (tabSep : Bool) -> TagEnv -> Props -> Rule True YState
  blockNode mi nOv tabSep env oprops st [] _ = eoi
  blockNode mi nOv tabSep env oprops st (c :: cs) sa@(SA r) =
    let n := maybe st.pos.col id nOv
     in if c == '-' && wordEnd cs
          then
            if tabSep
              then custom (oneChar st.pos) TabIndent
              else seqLoop env n (emit (SeqStart False oprops.anchor oprops.tag) st) (c :: cs) sa
        else if c == '?' && wordEnd cs
          then
            if tabSep
              then custom (oneChar st.pos) TabIndent
              else case expEntry env n (emit (MapStart False oprops.anchor oprops.tag) st) (c :: cs) sa of
                Fail0 e => Fail0 e
                Succ0 st1 r1 @{q1} => trans (blockMap env n st1 r1 (r @{q1})) q1
        else if c == ':' && wordEnd cs
          then
            if tabSep
              then custom (oneChar st.pos) TabIndent
              else
                let evs1 := emptyScalar (st.evs :< MapStart False oprops.anchor oprops.tag)
                 in case afterKey env n False noProps (YS (incCol st.pos) evs1) cs (r @{uncons Same}) of
                      Fail0 e => Fail0 e
                      Succ0 st1 r1 @{q1} =>
                        let 0 p1 := trans q1 (uncons Same)
                         in trans (blockMap env n st1 r1 (r @{p1})) p1
        else if c == '|' || c == '>'
          then case blockScalar (c == '>') mi (c :: cs) of
            Succ s rem @{prf} =>
              let sty := if c == '>' then Folded else Literal
               in Succ0 (YS (endPos st.pos prf) (st.evs :< Scalar oprops.anchor oprops.tag sty s)) rem
            Fail start errEnd err => Fail0 (boundedErr st.pos start errEnd err)
        else case cand False mi env noProps st.pos (c :: cs) sa of
          Fail0 e => Fail0 e
          Succ0 (pend, p1) r1 @{q1} =>
            let IL cnt tbw r2 w := inlineWhite r1
                p2   := addCol cnt p1
                0 pw := trans w q1
             in if colonBlock r2
                  then -- this node is a block mapping; `pend` its first key
                    if tabSep
                      then custom (oneChar st.pos) TabIndent
                    else if p1.line /= st.pos.line
                      then custom (BS st.pos p1) InvalidKey
                    else if isJust nOv && pendProps pend
                      then custom (BS st.pos p1) InvalidKey
                      else case r2 of
                        ':' :: r3 =>
                          let evs1 := flushPend (st.evs :< MapStart False oprops.anchor oprops.tag) pend
                              0 pc := trans (uncons Same) (trans w q1)
                           in case afterKey env n False noProps (YS (incCol p2) evs1) r3 (r @{pc}) of
                                Fail0 e => Fail0 e
                                Succ0 st4 r4 @{q4} =>
                                  let 0 p4 := trans q4 pc
                                   in trans (blockMap env n st4 r4 (r @{p4})) p4
                        _ => eoi
                  else case pend of
                    PFlow d => case patchFlow oprops d of
                      Left e   => custom (BS st.pos p1) e
                      Right d2 => case lineEnd (cnt > 0) p2 r2 of
                        Fail0 e => Fail0 e
                        Succ0 p3 r3 @{q3} =>
                          Succ0 (YS p3 (st.evs ++ d2)) r3 @{trans q3 pw}
                    PAlias a =>
                      if isNoProps oprops
                        then case lineEnd (cnt > 0) p2 r2 of
                          Fail0 e => Fail0 e
                          Succ0 p3 r3 @{q3} =>
                            Succ0 (YS p3 (st.evs :< Alias a)) r3 @{trans q3 pw}
                        else parseFail (oneChar st.pos) (Unknown "properties on alias node")
                    PProps pr => case mergeProps oprops pr of
                      Left e    => custom (BS st.pos p1) e
                      Right prm => case bsStart r2 of
                        Just f => case blockScalar f mi r2 of
                          Succ s rem @{prf} =>
                            let sty := if f then Folded else Literal
                             in Succ0 (YS (endPos p2 prf) (st.evs :< Scalar prm.anchor prm.tag sty s)) rem
                              @{trans prf pw}
                          Fail start errEnd err => Fail0 (boundedErr p2 start errEnd err)
                        Nothing =>
                          if breakStart r2
                            then case skipToContent r2 of
                              SR (L ind LContent tb) r3 prf3 =>
                                if ind >= mi
                                  then
                                    let 0 p3 := trans prf3 pw
                                     in succT (blockNode mi Nothing tb env prm (YS (endPos p2 prf3) st.evs) r3 (r @{p3})) @{p3}
                                  else Succ0 (YS p2 (emptyScalarP prm st.evs)) r2 @{pw}
                              SR _ _ _ => Succ0 (YS p2 (emptyScalarP prm st.evs)) r2 @{pw}
                            else if null r2
                              then Succ0 (YS p2 (emptyScalarP prm st.evs)) r2 @{pw}
                              else parseFail (oneChar p2) (Unknown "content after node properties")
                    PScalar pr Plain s => case mergeProps oprops pr of
                      Left e    => custom (BS st.pos p1) e
                      Right prm => case plainMore False mi s p2 r2 (r @{pw}) of
                        Fail0 e => Fail0 e
                        Succ0 (s2, p3) r3 @{q3} =>
                          if colonBlock r3
                            then custom (BS st.pos p3) InvalidKey
                            else
                              Succ0 (YS p3 (st.evs :< Scalar prm.anchor prm.tag Plain s2)) r3
                                @{trans q3 pw}
                    PScalar pr sty s => case mergeProps oprops pr of
                      Left e    => custom (BS st.pos p1) e
                      Right prm => case lineEnd (cnt > 0) p2 r2 of
                        Fail0 e => Fail0 e
                        Succ0 p3 r3 @{q3} =>
                          Succ0 (YS p3 (st.evs :< Scalar prm.anchor prm.tag sty s)) r3
                            @{trans q3 pw}

  ||| Entries of a block sequence anchored at column `n` [spec:
  ||| l+block-sequence], starting at a `- ` indicator. Emits the SeqEnd
  ||| when the indentation ends.
  seqLoop : TagEnv -> (n : Nat) -> Rule True YState
  seqLoop env n st ('-' :: cs) (SA r) =
    case seqEntry env n (YS (incCol st.pos) st.evs) cs (r @{uncons Same}) of
      Fail0 e => Fail0 e
      Succ0 st1 r1 @{q1} =>
        let 0 p1 := trans q1 (uncons Same)
         in case skipToContent r1 of
              SR (L ind LContent tb) r2 prf2 =>
                if ind == n && dashNext r2
                  then
                    if tb
                      then custom (oneChar $ endPos st1.pos prf2) TabIndent
                      else
                        let 0 pp := trans prf2 p1
                         in succT (seqLoop env n (YS (endPos st1.pos prf2) st1.evs) r2 (r @{pp})) @{pp}
                  else Succ0 (emit SeqEnd st1) r1 @{p1}
              SR _ _ _ => Succ0 (emit SeqEnd st1) r1 @{p1}
  seqLoop env n st (x :: _) _ = parseFail (oneChar st.pos) (Expected ["'-'"] (pack [x]))
  seqLoop env n st []       _ = eoi

  ||| A block sequence entry after its `- ` indicator [spec:
  ||| c-l-block-seq-entry]: same-line content (including compact
  ||| collections), a more indented node on following lines, or empty.
  seqEntry : TagEnv -> (n : Nat) -> Rule False YState
  seqEntry env n st cs sa@(SA r) =
    let IL cnt tbw r2 w := inlineWhite cs
        p2 := addCol cnt st.pos
     in case r2 of
          [] => Succ0 (YS p2 (emptyScalar st.evs)) [] @{w}
          x :: xs =>
            if isBreak x || x == '#'
              then case skipToContent (x :: xs) of
                SR (L ind LContent tb) r3 prf3 =>
                  if ind >= S n
                    then
                      let st3 := YS (endPos p2 prf3) st.evs
                       in case trans prf3 w of
                            Same     => weaken $ blockNode (S n) Nothing tb env noProps st3 r3 sa
                            Uncons u =>
                              weaken $ trans (blockNode (S n) Nothing tb env noProps st3 r3 (r @{uncons u}))
                                             (weaken (uncons u))
                    else Succ0 (YS p2 (emptyScalar st.evs)) (x :: xs) @{w}
                SR _ _ _ => Succ0 (YS p2 (emptyScalar st.evs)) (x :: xs) @{w}
              else
                let st2 := YS p2 st.evs
                 in case w of
                      Same     => weaken $ blockNode (S n) Nothing tbw env noProps st2 (x :: xs) sa
                      Uncons u =>
                        weaken $ trans (blockNode (S n) Nothing tbw env noProps st2 (x :: xs) (r @{uncons u}))
                                       (weaken (uncons u))

  ||| Further entries of a block mapping anchored at column `n` [spec:
  ||| l+block-mapping]: emits the MapEnd when the indentation ends.
  blockMap : TagEnv -> (n : Nat) -> Rule False YState
  blockMap env n st cs sa@(SA r) = case skipToContent cs of
    SR (L ind LContent tb) r2 prf2 =>
      if ind == n
        then
          if tb then custom (oneChar $ endPos st.pos prf2) TabIndent else
          let st2 := YS (endPos st.pos prf2) st.evs
           in case prf2 of
                Same => case mapEntry env n st2 r2 sa of
                  Fail0 e => Fail0 e
                  Succ0 st3 r3 @{q3} =>
                    trans (blockMap env n st3 r3 (r @{q3})) (weaken q3)
                Uncons u => case mapEntry env n st2 r2 (r @{uncons u}) of
                  Fail0 e => Fail0 e
                  Succ0 st3 r3 @{q3} =>
                    let 0 p3 := trans q3 (uncons u)
                     in trans (blockMap env n st3 r3 (r @{p3})) (weaken p3)
        else Succ0 (emit MapEnd st) cs
    SR _ _ _ => Succ0 (emit MapEnd st) cs

  ||| A single block mapping entry at indent `n` [spec:
  ||| ns-l-block-map-entry]: explicit (`? `), an empty key (`: `), or
  ||| an implicit single-line key followed by `:`.
  mapEntry : TagEnv -> (n : Nat) -> Rule True YState
  mapEntry env n st [] _ = eoi
  mapEntry env n st (c :: cs) sa@(SA r) =
    if c == '?' && wordEnd cs
      then expEntry env n st (c :: cs) sa
    else if c == ':' && wordEnd cs
      then case afterKey env n False noProps (YS (incCol st.pos) (emptyScalar st.evs)) cs (r @{uncons Same}) of
        Fail0 e => Fail0 e
        Succ0 st1 r1 @{q1} => Succ0 st1 r1 @{trans q1 (uncons Same)}
    else case cand False (S n) env noProps st.pos (c :: cs) sa of
      Fail0 e => Fail0 e
      Succ0 (pend, p1) r1 @{q1} =>
        let IL cnt tbw r2 w := inlineWhite r1
            p2   := addCol cnt p1
            0 pw := trans w q1
         in if colonBlock r2
              then
                if p1.line /= st.pos.line
                  then custom (BS st.pos p1) InvalidKey
                  else case r2 of
                    ':' :: r3 =>
                      let 0 pc := trans (uncons Same) (trans w q1)
                       in case afterKey env n False noProps (YS (incCol p2) (flushPend st.evs pend)) r3 (r @{pc}) of
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
  expEntry : TagEnv -> (n : Nat) -> Rule True YState
  expEntry env n st ('?' :: cs) sa@(SA r) =
    let IL cnt tbw r2 w := inlineWhite cs
        p2 := addCol cnt (incCol st.pos)
        keyRes : Result0 True Char ('?' :: cs) (BoundedErr YErr) YState :=
          case r2 of
            [] => Succ0 (YS p2 (emptyScalar st.evs)) [] @{trans w (uncons Same)}
            x :: xs =>
              if isBreak x || x == '#'
                then case skipToContent (x :: xs) of
                  SR (L ind LContent tb) r3 prf3 =>
                    -- a zero-indented sequence may sit at the same
                    -- indent as the `?` indicator [spec: seq-spaces]
                    if ind >= S n || (ind == n && dashNext r3)
                      then
                        let 0 p3 := trans prf3 (trans w (uncons Same))
                         in succT (blockNode (S n) Nothing tb env noProps (YS (endPos p2 prf3) st.evs) r3 (r @{p3})) @{p3}
                      else Succ0 (YS p2 (emptyScalar st.evs)) (x :: xs) @{trans w (uncons Same)}
                  SR _ _ _ => Succ0 (YS p2 (emptyScalar st.evs)) (x :: xs) @{trans w (uncons Same)}
                else
                  let 0 pw := trans w (uncons Same)
                   in succT (blockNode (S n) Nothing tbw env noProps (YS p2 st.evs) (x :: xs) (r @{pw})) @{pw}
     in case keyRes of
          Fail0 e => Fail0 e
          Succ0 stK remK @{qK} => case skipToContent remK of
            SR (L ind LContent tb) rV prfV =>
              if ind == n && colonBlock rV
                then
                  if tb then custom (oneChar $ endPos stK.pos prfV) TabIndent else
                  case rV of
                  ':' :: rV2 =>
                    let pV   := incCol (endPos stK.pos prfV)
                        0 pc := trans (uncons Same) (trans prfV qK)
                     in case afterKey env n True noProps (YS pV stK.evs) rV2 (r @{pc}) of
                          Fail0 e => Fail0 e
                          Succ0 stF rF @{qF} => Succ0 stF rF @{trans qF pc}
                  _ => eoi
                else Succ0 ({evs $= emptyScalar} stK) remK @{qK}
            SR _ _ _ => Succ0 ({evs $= emptyScalar} stK) remK @{qK}
  expEntry env n st (x :: _) _ = parseFail (oneChar st.pos) (Expected ["'?'"] (pack [x]))
  expEntry env n st []       _ = eoi

  ||| The value of a block mapping entry, after its `:` indicator
  ||| [spec: c-l-block-map-implicit-value]: an inline value on the same
  ||| line, a block node on following lines, a sequence at the same
  ||| indent (the "seq-spaces" exception), or empty. `pr` holds
  ||| properties already parsed on the indicator's line.
  afterKey : TagEnv -> (n : Nat) -> (cpt : Bool) -> Props -> Rule False YState
  afterKey env n cpt pr st cs sa@(SA r) =
    let IL cnt tbw r2 w := inlineWhite cs
        p2 := addCol cnt st.pos
     in case r2 of
          [] => Succ0 (YS p2 (emptyScalarP pr st.evs)) [] @{w}
          x :: xs =>
            if x == '&' || x == '!'
              then case w of
                Same     => case pProps env pr p2 (x :: xs) sa of
                  Fail0 e => Fail0 e
                  Succ0 (pr2, p3) r3 @{q3} =>
                    trans (afterKey env n cpt pr2 (YS p3 st.evs) r3 (r @{q3})) (weaken q3)
                Uncons u => case pProps env pr p2 (x :: xs) (r @{uncons u}) of
                  Fail0 e => Fail0 e
                  Succ0 (pr2, p3) r3 @{q3} =>
                    let 0 pc := trans q3 (uncons u)
                     in trans (afterKey env n cpt pr2 (YS p3 st.evs) r3 (r @{pc})) (weaken pc)
            else if isBreak x || x == '#'
              then case skipToContent (x :: xs) of
                SR (L ind LContent tb) r3 prf3 =>
                  let st3 := YS (endPos p2 prf3) st.evs
                   in if ind >= S n && propStart r3 && propsOnlyLine r3
                        -- properties on their own line: they may yet
                        -- belong to a sequence at the parent's indent
                        -- [spec: seq-spaces], so continue in this rule
                        then case trans prf3 w of
                          Same => case pProps env pr st3.pos r3 sa of
                            Fail0 e => Fail0 e
                            Succ0 (pr2, p4) r4 @{q4} =>
                              trans (afterKey env n cpt pr2 (YS p4 st.evs) r4 (r @{q4})) (weaken q4)
                          Uncons u => case pProps env pr st3.pos r3 (r @{uncons u}) of
                            Fail0 e => Fail0 e
                            Succ0 (pr2, p4) r4 @{q4} =>
                              let 0 pc := trans q4 (uncons u)
                               in trans (afterKey env n cpt pr2 (YS p4 st.evs) r4 (r @{pc})) (weaken pc)
                      else if ind >= S n
                        then case trans prf3 w of
                          Same     => weaken $ blockNode (S n) Nothing tb env pr st3 r3 sa
                          Uncons u =>
                            weaken $ trans (blockNode (S n) Nothing tb env pr st3 r3 (r @{uncons u}))
                                           (weaken (uncons u))
                        else if ind == n && dashNext r3
                          then
                            let st3s := emit (SeqStart False pr.anchor pr.tag) st3
                             in case trans prf3 w of
                                  Same     => weaken $ seqLoop env n st3s r3 sa
                                  Uncons u =>
                                    weaken $ trans (seqLoop env n st3s r3 (r @{uncons u}))
                                                   (weaken (uncons u))
                          else Succ0 (YS p2 (emptyScalarP pr st.evs)) (x :: xs) @{w}
                SR _ _ _ => Succ0 (YS p2 (emptyScalarP pr st.evs)) (x :: xs) @{w}
              else if cpt
                -- an explicit entry's value: compact collections are
                -- allowed on the same line [spec: s-l+block-indented]
                then case w of
                  Same     => weaken $ blockNode (S n) Nothing tbw env pr (YS p2 st.evs) (x :: xs) sa
                  Uncons u =>
                    weaken $ trans (blockNode (S n) Nothing tbw env pr (YS p2 st.evs) (x :: xs) (r @{uncons u}))
                                   (weaken (uncons u))
                else case w of
                  Same     => weaken $ inlineVal env n pr (YS p2 st.evs) (x :: xs) sa
                  Uncons u =>
                    weaken $ trans (inlineVal env n pr (YS p2 st.evs) (x :: xs) (r @{uncons u}))
                                   (weaken (uncons u))

  ||| A mapping value on the same line as its `:` indicator: a flow
  ||| node or a block scalar [spec: s-l+flow-in-block, s-l+block-scalar].
  inlineVal : TagEnv -> (n : Nat) -> Props -> Rule True YState
  inlineVal env n pr st [] _ = eoi
  inlineVal env n pr st (c :: cs) sa@(SA r) =
    if c == '[' || c == '{' || c == '\'' || c == '"' || c == '*'
      then case flowNode False (S n) env pr st (c :: cs) sa of
        Fail0 e => Fail0 e
        Succ0 st1 r1 @{q1} => case lineEnd False st1.pos r1 of
          Fail0 e => Fail0 e
          Succ0 p2 r2 @{q2} => Succ0 (YS p2 st1.evs) r2 @{trans q2 q1}
      else if c == '|' || c == '>'
        then case blockScalar (c == '>') (S n) (c :: cs) of
          Succ s rem @{prf} =>
            let sty := if c == '>' then Folded else Literal
             in Succ0 (YS (endPos st.pos prf) (st.evs :< Scalar pr.anchor pr.tag sty s)) rem
          Fail start errEnd err => Fail0 (boundedErr st.pos start errEnd err)
      else if isPlainFirst False c cs
        then case plainSegment False (c :: cs) of
          Succ s rem @{prf} =>
            case plainMore False (S n) s (move st.pos prf) rem (r @{prf}) of
              Fail0 e => Fail0 e
              Succ0 (s2, p2) r2 @{q2} =>
                if colonBlock r2
                  then custom (BS st.pos p2) InvalidKey
                  else
                    Succ0 (YS p2 (st.evs :< Scalar pr.anchor pr.tag Plain s2)) r2
                      @{trans q2 prf}
          Fail start errEnd err => Fail0 (boundedErr st.pos start errEnd err)
        else parseFail (oneChar st.pos) (Unknown $ pack [c])

--------------------------------------------------------------------------------
--          Documents
--------------------------------------------------------------------------------

mutual
  ||| The documents of a YAML stream [spec: l-yaml-stream]. `ab` is
  ||| true where a document may start without an explicit `---` marker:
  ||| at the start of the stream and after a `...` marker.
  stream : (ab : Bool) -> TagEnv -> (sawYaml : Bool) -> Rule False YState
  stream ab env sy st cs sa@(SA r) = case skipToContent cs of
    SR (L _ LEnd _) rem prf =>
      if dirty
        then parseFail (oneChar $ endPos st.pos prf) (Expected ["'---'"] "end of input")
        else Succ0 ({pos := endPos st.pos prf} st) rem @{prf}
    SR (L _ LDocEnd _) rem prf =>
      -- a document end marker without an open document is consumed
      -- silently, but pending directives require a document
      -- [spec: l-yaml-stream]
      if dirty
        then parseFail (oneChar $ endPos st.pos prf) (Expected ["'---'"] "'...'")
        else
          let st1 := YS (endPos st.pos prf) st.evs
           in case prf of
                Same     => weaken $ docSuffix False st1 cs sa
                Uncons u =>
                  weaken $ trans (docSuffix False st1 rem (r @{uncons u})) (weaken (uncons u))
    SR (L _ LDocStart _) rem prf =>
      let st1 := emit (DocStart True) ({pos := endPos st.pos prf} st)
       in case prf of
            Same     => weaken $ docStart env st1 cs sa
            Uncons u =>
              weaken $ trans (docStart env st1 rem (r @{uncons u})) (weaken (uncons u))
    SR (L ind LContent tb) rem prf =>
      let pC  := endPos st.pos prf
          st1 := {pos := pC} st
       in if bomStart rem && ind == 0
            then case prf of
              Same     => weaken $ bomDoc ab env sy st1 cs sa
              Uncons u =>
                weaken $ trans (bomDoc ab env sy st1 rem (r @{uncons u})) (weaken (uncons u))
          else if dirStart rem && ind == 0
            then
              if ab || dirty
                then case prf of
                  Same     => weaken $ dirDoc ab env sy st1 cs sa
                  Uncons u =>
                    weaken $ trans (dirDoc ab env sy st1 rem (r @{uncons u})) (weaken (uncons u))
                else custom (oneChar pC) TrailingContent
          else if ab && not dirty
            then
              let st2 := emit (DocStart False) st1
               in case prf of
                    Same     => weaken $ bareDoc tb env st2 cs sa
                    Uncons u =>
                      weaken $ trans (bareDoc tb env st2 rem (r @{uncons u})) (weaken (uncons u))
            else custom (oneChar pC) TrailingContent

    where
      dirty : Bool
      dirty = sy || not (null env.handles)

      bomStart : List Char -> Bool
      bomStart ('\xfeff' :: _) = True
      bomStart _               = False

      dirStart : List Char -> Bool
      dirStart ('%' :: _) = True
      dirStart _          = False

  ||| A byte order mark before a document [spec: l-document-prefix].
  bomDoc : (ab : Bool) -> TagEnv -> (sawYaml : Bool) -> Rule True YState
  bomDoc ab env sy st ('\xfeff' :: t) (SA r) =
    succT (stream ab env sy ({pos $= incCol} st) t (r @{uncons Same})) @{uncons Same}
  bomDoc _ _ _ st _ _ = eoi

  ||| A directive line before a document [spec: l-directive].
  dirDoc : (ab : Bool) -> TagEnv -> (sawYaml : Bool) -> Rule True YState
  dirDoc ab env sy st cs (SA r) = case dirLine cs of
    Succ ln rem @{prf} =>
      let pos2 := endPos st.pos prf
       in case parseDirective env sy ln of
            Left e             => custom (BS st.pos pos2) e
            Right (env2, sy2)  =>
              succT (stream ab env2 sy2 (YS pos2 st.evs) rem (r @{prf})) @{prf}
    Fail start errEnd err => Fail0 (boundedErr st.pos start errEnd err)

  ||| An explicit document, at its `---` marker (the DocStart event has
  ||| already been emitted).
  docStart : TagEnv -> Rule True YState
  docStart env st ('-' :: '-' :: '-' :: t) (SA r) =
    let IL cnt tbw r2 w := inlineWhite t
        p2 := addCol cnt (addCol 3 st.pos)
     in case r2 of
          [] =>
            Succ0 (YS p2 (emptyScalar st.evs)) []
              @{trans w (uncons $ uncons $ uncons Same)}
          x :: xs =>
            if isBreak x || x == '#'
              then case skipToContent (x :: xs) of
                SR (L ind LContent tb) r3 prf3 =>
                  let 0 pc := trans prf3 (trans w (uncons $ uncons $ uncons Same))
                   in case blockNode 0 Nothing tb env noProps (YS (endPos p2 prf3) st.evs) r3 (r @{pc}) of
                        Fail0 e => Fail0 e
                        Succ0 st4 r4 @{q4} =>
                          let 0 p4 := trans q4 pc
                           in trans (docTail st4 r4 (r @{p4})) p4
                SR _ _ _ =>
                  -- an empty document; docTail handles what follows
                  let 0 p3 := trans w (uncons $ uncons $ uncons Same)
                   in trans (docTail (YS p2 (emptyScalar st.evs)) (x :: xs) (r @{p3})) p3
              else
                let 0 p3 := trans w (uncons $ uncons $ uncons Same)
                 in case blockNode 0 (Just 0) tbw env noProps (YS p2 st.evs) (x :: xs) (r @{p3}) of
                      Fail0 e => Fail0 e
                      Succ0 st4 r4 @{q4} =>
                        let 0 p4 := trans q4 p3
                         in trans (docTail st4 r4 (r @{p4})) p4
  docStart env st _ _ = eoi

  ||| A document starting without a `---` marker (the DocStart event
  ||| has already been emitted).
  bareDoc : (tabSep : Bool) -> TagEnv -> Rule True YState
  bareDoc tabSep env st cs sa@(SA r) = case blockNode 0 Nothing tabSep env noProps st cs sa of
    Fail0 e => Fail0 e
    Succ0 st1 r1 @{q1} => trans (docTail st1 r1 (r @{q1})) q1

  ||| After a document's root node: an explicit `...` end, the start of
  ||| the next document, the end of the stream, or an error.
  docTail : Rule False YState
  docTail st cs sa@(SA r) = case skipToContent cs of
    SR (L _ LEnd _) rem prf =>
      Succ0 (YS (endPos st.pos prf) (st.evs :< DocEnd False)) rem @{prf}
    SR (L _ LDocStart _) rem prf =>
      let st1 := emit (DocEnd False) ({pos := endPos st.pos prf} st)
       in case prf of
            Same     => stream False defaultEnv False st1 cs sa
            Uncons u =>
              trans (stream False defaultEnv False st1 rem (r @{uncons u})) (weaken (uncons u))
    SR (L _ LDocEnd _) rem prf =>
      let st1 := YS (endPos st.pos prf) st.evs
       in case prf of
            Same     => weaken $ docSuffix True st1 cs sa
            Uncons u =>
              weaken $ trans (docSuffix True st1 rem (r @{uncons u})) (weaken (uncons u))
    SR (L _ LContent tb) rem prf =>
      custom (oneChar $ endPos st.pos prf) TrailingContent

  ||| A `...` document end marker [spec: l-document-suffix]. The DocEnd
  ||| event is only emitted when the marker closes an open document.
  docSuffix : (emitEnd : Bool) -> Rule True YState
  docSuffix emitEnd st ('.' :: '.' :: '.' :: t) (SA r) =
    let evs1 := if emitEnd then st.evs :< DocEnd True else st.evs
        st1  := YS (addCol 3 st.pos) evs1
     in case lineEnd False st1.pos t of
          Fail0 e => Fail0 e
          Succ0 p2 r2 @{q2} =>
            let 0 pp := trans q2 (uncons $ uncons $ uncons Same)
             in succT (stream True defaultEnv False (YS p2 st1.evs) r2 (r @{pp})) @{pp}
  docSuffix _ st _ _ = eoi

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
  let cs := normalize (unpack str)
   in case stream True defaultEnv False (YS begin [<StreamStart]) cs suffixAcc of
        Succ0 st _ => Right (st.evs <>> [StreamEnd])
        Fail0 err  => Left (toParseError o (pack cs) err)
