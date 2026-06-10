module Text.YAML.Compose

import Data.List.Suffix
import Data.List.Suffix.Result0
import Data.SortedMap
import Data.SortedSet
import Text.YAML.Parser
import public Text.YAML.Node
import public Text.YAML.Types

%default total

--------------------------------------------------------------------------------
--          Composing
--------------------------------------------------------------------------------

0 Anchors : Type
Anchors = SortedMap Anchor Node

anchored : Maybe Anchor -> Node -> Anchors -> Anchors
anchored Nothing  _ as = as
anchored (Just a) n as = insert a n as

livePlus : Maybe Anchor -> SortedSet Anchor -> SortedSet Anchor
livePlus Nothing  live = live
livePlus (Just a) live = insert a live

hasKey : Node -> SnocList (Node, Node) -> Bool
hasKey k [<]              = False
hasKey k (ps :< (k2, _))  = k == k2 || hasKey k ps

||| A composing rule over the remaining events, consuming a strict
||| prefix when `b` is `True`. Errors carry the bounds of the events
||| they refer to.
|||
||| Totality: unlike the character-level parser, every node consumes at
||| least one event, so all rules below are strict and the `SuffixAcc`
||| recursion is straightforward.
0 CRule : Bool -> Type -> Type
CRule b a =
     (es : List (Bounded Event))
  -> (0 acc : SuffixAcc es)
  -> Result0 b (Bounded Event) es (BoundedErr YErr) a

-- Anchors become visible once their node is complete: scalars insert
-- immediately, collections only after their children have composed, so
-- sibling references (`[&a 1, *a]`) resolve while self references
-- (`&a [*a]`) fail. The `live` set holds the anchors of enclosing,
-- still open collections; it flows downward only (lexical scoping) and
-- serves to distinguish `CyclicAlias` from `UndefinedAlias`.
mutual
  ||| A single node: scalar, alias, sequence or mapping. Returns the
  ||| node together with its full source span.
  node :
       Schema
    -> Anchors
    -> (live : SortedSet Anchor)
    -> CRule True (Node, Bounds, Anchors)
  node sch as live (B (Scalar ma t sty s) bs :: es) _ =
    let n := NScalar (scalarTag sch t sty s) sty s
     in Succ0 (n, bs, anchored ma n as) es
  node sch as live (B (Alias a) bs :: es) _ = case lookup a as of
    Just n  => Succ0 (n, bs, as) es
    Nothing =>
      custom bs $ if contains a live then CyclicAlias a else UndefinedAlias a
  node sch as live (B (SeqStart _ ma t) bs :: es) (SA r) =
    case seqItems sch as (livePlus ma live) [<] es (r @{uncons Same}) of
      Fail0 e => Fail0 e
      Succ0 (ns, be, as2) rest @{q} =>
        let n := NSeq (collTag sch t TSeq) ns
         in Succ0 (n, bs <+> be, anchored ma n as2) rest @{trans q (uncons Same)}
  node sch as live (B (MapStart _ ma t) bs :: es) (SA r) =
    case mapItems sch as (livePlus ma live) [<] es (r @{uncons Same}) of
      Fail0 e => Fail0 e
      Succ0 (ps, be, as2) rest @{q} =>
        let n := NMap (collTag sch t TMap) ps
         in Succ0 (n, bs <+> be, anchored ma n as2) rest @{trans q (uncons Same)}
  node _ _ _ (B e bs :: _) _ = custom bs (UnexpectedEvent (printEvent e))
  node _ _ _ []            _ = custom NoBounds UnexpectedEnd

  ||| The remaining entries of a sequence, up to its end event, whose
  ||| bounds are returned.
  seqItems :
       Schema
    -> Anchors
    -> SortedSet Anchor
    -> SnocList Node
    -> CRule True (List Node, Bounds, Anchors)
  seqItems sch as live acc (B SeqEnd be :: es) _ = Succ0 (acc <>> [], be, as) es
  seqItems sch as live acc []                  _ = custom NoBounds UnexpectedEnd
  seqItems sch as live acc es sa@(SA r)          = case node sch as live es sa of
    Fail0 e => Fail0 e
    Succ0 (n, _, as2) rest @{q} =>
      succT $ seqItems sch as2 live (acc :< n) rest (r @{q})

  ||| The remaining entries of a mapping, up to its end event, whose
  ||| bounds are returned.
  mapItems :
       Schema
    -> Anchors
    -> SortedSet Anchor
    -> SnocList (Node, Node)
    -> CRule True (List (Node, Node), Bounds, Anchors)
  mapItems sch as live acc (B MapEnd be :: es) _ = Succ0 (acc <>> [], be, as) es
  mapItems sch as live acc []                  _ = custom NoBounds UnexpectedEnd
  mapItems sch as live acc es sa@(SA r)          = case node sch as live es sa of
    Fail0 e => Fail0 e
    Succ0 (k, kbs, as2) rest @{q} =>
      if hasKey k acc
        then custom kbs (DuplicateKey (canon k))
        else case node sch as2 live rest (r @{q}) of
          Fail0 e => Fail0 e
          Succ0 (v, _, as3) rest2 @{q2} =>
            let 0 pp := trans q2 q
             in succT $ mapItems sch as3 live (acc :< (k, v)) rest2 (r @{pp})

--------------------------------------------------------------------------------
--          Entry Points
--------------------------------------------------------------------------------

||| Composes an event stream into one node tree per document: aliases
||| are substituted by the nodes they reference (sharing structure),
||| tags of untagged nodes are resolved against the given schema, and
||| mapping keys are checked for uniqueness. Anchors are scoped to
||| their document; redefining an anchor shadows the previous node.
|||
||| Errors carry the source bounds of the events they refer to; pair
||| them with the (line break normalized) input via `toParseError` for
||| a rendered excerpt, or use `parseDocsWith`, which does so.
export
composeWith : Schema -> List (Bounded Event) -> Either (BoundedErr YErr) (List Node)
composeWith sch (B StreamStart _ :: es) = go [<] es suffixAcc
  where
    go :
         SnocList Node
      -> (es : List (Bounded Event))
      -> (0 acc : SuffixAcc es)
      -> Either (BoundedErr YErr) (List Node)
    go acc (B StreamEnd _ :: [])          _      = Right (acc <>> [])
    go acc (B StreamEnd _ :: B e bs :: _) _      =
      custom bs (UnexpectedEvent (printEvent e))
    go acc (B (DocStart _) _ :: es2)      (SA r) =
      case node sch empty empty es2 (r @{uncons Same}) of
        Fail0 e => Left e
        Succ0 (n, _, _) (B (DocEnd _) _ :: rest) @{q} =>
          let 0 pp := trans (uncons q) (uncons Same)
           in go (acc :< n) rest (r @{pp})
        Succ0 _ (B e bs :: _) => custom bs (UnexpectedEvent (printEvent e))
        Succ0 _ []            => custom NoBounds UnexpectedEnd
    go acc (B e bs :: _) _ = custom bs (UnexpectedEvent (printEvent e))
    go acc []            _ = custom NoBounds UnexpectedEnd
composeWith _ (B e bs :: _) = custom bs (UnexpectedEvent (printEvent e))
composeWith _ []            = custom NoBounds UnexpectedEnd

||| `composeWith` under the core schema.
export %inline
compose : List (Bounded Event) -> Either (BoundedErr YErr) (List Node)
compose = composeWith Core

||| Parses and composes a YAML stream into one node tree per document.
export
parseDocsWith : Schema -> Origin -> String -> Either (ParseError YErr) (List Node)
parseDocsWith sch o s =
  case parseEvents o s of
    Left e   => Left e
    Right es => case composeWith sch es of
      Left e   => Left (toParseError o (normalized s) e)
      Right ns => Right ns

||| `parseDocsWith` under the core schema.
export %inline
parseDocs : Origin -> String -> Either (ParseError YErr) (List Node)
parseDocs = parseDocsWith Core
