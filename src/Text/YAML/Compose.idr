module Text.YAML.Compose

import Data.List.Suffix
import Data.List.Suffix.Result0
import Data.SortedMap
import Data.SortedSet
import Derive.Prelude
import Text.YAML.Parser
import public Text.YAML.Node
import public Text.YAML.Types

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Errors
--------------------------------------------------------------------------------

||| Errors composing an event stream into node trees.
|||
||| Compose errors carry no source positions: events do not remember
||| where they were parsed.
public export
data ComposeErr : Type where
  ||| The event sequence is malformed. Streams produced by
  ||| `parseEvents` never trigger this.
  UnexpectedEvent : Event -> ComposeErr

  ||| The events ended in the middle of a node or document.
  UnexpectedEnd   : ComposeErr

  ||| An alias referencing an anchor that is not in scope.
  UndefinedAlias  : Anchor -> ComposeErr

  ||| An alias referencing an anchor whose node is still being
  ||| composed, as in `&a [*a]`: such cyclic structures cannot be
  ||| represented as finite trees.
  CyclicAlias     : Anchor -> ComposeErr

  ||| A mapping with two equal keys [spec 3.2.1.3].
  DuplicateKey    : Node -> ComposeErr

%runElab derive "ComposeErr" [Show,Eq]

export
Interpolation ComposeErr where
  interpolate (UnexpectedEvent e) = "unexpected event: \{printEvent e}"
  interpolate UnexpectedEnd       = "unexpected end of events"
  interpolate (UndefinedAlias a)  = "undefined alias: *\{a}"
  interpolate (CyclicAlias a)     = "alias *\{a} refers to its own ancestor"
  interpolate (DuplicateKey k)    = "duplicate mapping key: \{canon k}"

||| Errors loading YAML documents: parsing or composing.
public export
data YAMLErr : Type where
  YParse   : ParseError YErr -> YAMLErr
  YCompose : ComposeErr -> YAMLErr

export
Interpolation YAMLErr where
  interpolate (YParse e)   = interpolate e
  interpolate (YCompose e) = interpolate e

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
||| prefix when `b` is `True`.
|||
||| Totality: unlike the character-level parser, every node consumes at
||| least one event, so all rules below are strict and the `SuffixAcc`
||| recursion is straightforward.
0 CRule : Bool -> Type -> Type
CRule b a =
     (es : List Event)
  -> (0 acc : SuffixAcc es)
  -> Result0 b Event es ComposeErr a

-- Anchors become visible once their node is complete: scalars insert
-- immediately, collections only after their children have composed, so
-- sibling references (`[&a 1, *a]`) resolve while self references
-- (`&a [*a]`) fail. The `live` set holds the anchors of enclosing,
-- still open collections; it flows downward only (lexical scoping) and
-- serves to distinguish `CyclicAlias` from `UndefinedAlias`.
mutual
  ||| A single node: scalar, alias, sequence or mapping.
  node :
       Schema
    -> Anchors
    -> (live : SortedSet Anchor)
    -> CRule True (Node, Anchors)
  node sch as live (Scalar ma t sty s :: es) _ =
    let n := NScalar (scalarTag sch t sty s) sty s
     in Succ0 (n, anchored ma n as) es
  node sch as live (Alias a :: es) _ = case lookup a as of
    Just n  => Succ0 (n, as) es
    Nothing =>
      Fail0 $ if contains a live then CyclicAlias a else UndefinedAlias a
  node sch as live (SeqStart _ ma t :: es) (SA r) =
    case seqItems sch as (livePlus ma live) [<] es (r @{uncons Same}) of
      Fail0 e => Fail0 e
      Succ0 (ns, as2) rest @{q} =>
        let n := NSeq (collTag sch t TSeq) ns
         in Succ0 (n, anchored ma n as2) rest @{trans q (uncons Same)}
  node sch as live (MapStart _ ma t :: es) (SA r) =
    case mapItems sch as (livePlus ma live) [<] es (r @{uncons Same}) of
      Fail0 e => Fail0 e
      Succ0 (ps, as2) rest @{q} =>
        let n := NMap (collTag sch t TMap) ps
         in Succ0 (n, anchored ma n as2) rest @{trans q (uncons Same)}
  node _ _ _ (e :: _) _ = Fail0 (UnexpectedEvent e)
  node _ _ _ []       _ = Fail0 UnexpectedEnd

  ||| The remaining entries of a sequence, up to its end event.
  seqItems :
       Schema
    -> Anchors
    -> SortedSet Anchor
    -> SnocList Node
    -> CRule True (List Node, Anchors)
  seqItems sch as live acc (SeqEnd :: es) _ = Succ0 (acc <>> [], as) es
  seqItems sch as live acc []             _ = Fail0 UnexpectedEnd
  seqItems sch as live acc es sa@(SA r)     = case node sch as live es sa of
    Fail0 e => Fail0 e
    Succ0 (n, as2) rest @{q} =>
      succT $ seqItems sch as2 live (acc :< n) rest (r @{q})

  ||| The remaining entries of a mapping, up to its end event.
  mapItems :
       Schema
    -> Anchors
    -> SortedSet Anchor
    -> SnocList (Node, Node)
    -> CRule True (List (Node, Node), Anchors)
  mapItems sch as live acc (MapEnd :: es) _ = Succ0 (acc <>> [], as) es
  mapItems sch as live acc []             _ = Fail0 UnexpectedEnd
  mapItems sch as live acc es sa@(SA r)     = case node sch as live es sa of
    Fail0 e => Fail0 e
    Succ0 (k, as2) rest @{q} =>
      if hasKey k acc
        then Fail0 (DuplicateKey k)
        else case node sch as2 live rest (r @{q}) of
          Fail0 e => Fail0 e
          Succ0 (v, as3) rest2 @{q2} =>
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
export
composeWith : Schema -> List Event -> Either ComposeErr (List Node)
composeWith sch (StreamStart :: es) = go [<] es suffixAcc
  where
    go :
         SnocList Node
      -> (es : List Event)
      -> (0 acc : SuffixAcc es)
      -> Either ComposeErr (List Node)
    go acc (StreamEnd :: [])     _      = Right (acc <>> [])
    go acc (StreamEnd :: e :: _) _      = Left (UnexpectedEvent e)
    go acc (DocStart _ :: es2)   (SA r) =
      case node sch empty empty es2 (r @{uncons Same}) of
        Fail0 e => Left e
        Succ0 (n, _) (DocEnd _ :: rest) @{q} =>
          let 0 pp := trans (uncons q) (uncons Same)
           in go (acc :< n) rest (r @{pp})
        Succ0 _ (e :: _) => Left (UnexpectedEvent e)
        Succ0 _ []       => Left UnexpectedEnd
    go acc (e :: _) _ = Left (UnexpectedEvent e)
    go acc []       _ = Left UnexpectedEnd
composeWith _ (e :: _) = Left (UnexpectedEvent e)
composeWith _ []       = Left UnexpectedEnd

||| `composeWith` under the core schema.
export %inline
compose : List Event -> Either ComposeErr (List Node)
compose = composeWith Core

||| Parses and composes a YAML stream into one node tree per document.
export
parseDocsWith : Schema -> Origin -> String -> Either YAMLErr (List Node)
parseDocsWith sch o s =
  case parseEvents o s of
    Left e   => Left (YParse e)
    Right es => case composeWith sch es of
      Left e   => Left (YCompose e)
      Right ns => Right ns

||| `parseDocsWith` under the core schema.
export %inline
parseDocs : Origin -> String -> Either YAMLErr (List Node)
parseDocs = parseDocsWith Core
