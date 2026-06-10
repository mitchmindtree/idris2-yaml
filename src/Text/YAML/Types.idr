module Text.YAML.Types

import Data.List
import Derive.Prelude
import public Text.ParseError

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Events
--------------------------------------------------------------------------------

||| Name given in a node's `&anchor` property or referenced
||| by an `*alias` node.
public export
0 Anchor : Type
Anchor = String

||| The presentation style of a scalar node.
public export
data Style : Type where
  ||| An unquoted scalar
  Plain   : Style

  ||| A 'single quoted' scalar
  SingleQ : Style

  ||| A "double quoted" scalar
  DoubleQ : Style

  ||| A literal (`|`) block scalar
  Literal : Style

  ||| A folded (`>`) block scalar
  Folded  : Style

%runElab derive "Style" [Show,Eq]

||| A node's tag property.
public export
data Tag : Type where
  ||| No tag property was given.
  NoTag    : Tag

  ||| The `!` non-specific tag.
  NonSpec  : Tag

  ||| A resolved tag: shorthands have been expanded via the active
  ||| `%TAG` handles, verbatim tags (`!<...>`) are taken as given.
  Verbatim : String -> Tag

%runElab derive "Tag" [Show,Eq]

||| A YAML parse event.
|||
||| A well-formed event stream follows this grammar:
|||
||| ```
||| stream   ::= StreamStart document* StreamEnd
||| document ::= DocStart node DocEnd
||| node     ::= Alias | Scalar
|||            | SeqStart node* SeqEnd
|||            | MapStart (node node)* MapEnd
||| ```
public export
data Event : Type where
  StreamStart : Event
  StreamEnd   : Event
  DocStart    : (explicit : Bool) -> Event
  DocEnd      : (explicit : Bool) -> Event
  SeqStart    : (flow : Bool) -> Maybe Anchor -> Tag -> Event
  SeqEnd      : Event
  MapStart    : (flow : Bool) -> Maybe Anchor -> Tag -> Event
  MapEnd      : Event
  Scalar      : Maybe Anchor -> Tag -> Style -> String -> Event
  Alias       : Anchor -> Event

%runElab derive "Event" [Show,Eq]

--------------------------------------------------------------------------------
--          Event Printing
--------------------------------------------------------------------------------

escape : SnocList Char -> Char -> SnocList Char
escape sc '\\' = sc :< '\\' :< '\\'
escape sc '\0' = sc :< '\\' :< '0'
escape sc '\b' = sc :< '\\' :< 'b'
escape sc '\n' = sc :< '\\' :< 'n'
escape sc '\r' = sc :< '\\' :< 'r'
escape sc '\t' = sc :< '\\' :< 't'
escape sc c    = sc :< c

value : String -> String
value s = pack (foldl escape [<] (unpack s) <>> [])

flow : String -> Bool -> String
flow s True  = " " ++ s
flow _ False = ""

anchor : Maybe Anchor -> String
anchor Nothing  = ""
anchor (Just a) = " &" ++ a

tag : Tag -> String
tag NoTag        = ""
tag NonSpec      = " <!>"
tag (Verbatim t) = " <" ++ t ++ ">"

sigil : Style -> Char
sigil Plain   = ':'
sigil SingleQ = '\''
sigil DoubleQ = '"'
sigil Literal = '|'
sigil Folded  = '>'

||| Prints an event in the format used by the YAML test suite's
||| `test.event` files: https://github.com/yaml/yaml-test-suite
export
printEvent : Event -> String
printEvent StreamStart      = "+STR"
printEvent StreamEnd        = "-STR"
printEvent (DocStart True)  = "+DOC ---"
printEvent (DocStart False) = "+DOC"
printEvent (DocEnd True)    = "-DOC ..."
printEvent (DocEnd False)   = "-DOC"
printEvent (SeqStart f a t) = "+SEQ" ++ flow "[]" f ++ anchor a ++ tag t
printEvent SeqEnd           = "-SEQ"
printEvent (MapStart f a t) = "+MAP" ++ flow "{}" f ++ anchor a ++ tag t
printEvent MapEnd           = "-MAP"
printEvent (Scalar a t s v) =
  "=VAL" ++ anchor a ++ tag t ++ " " ++ singleton (sigil s) ++ value v
printEvent (Alias a)        = "=ALI *" ++ a

--------------------------------------------------------------------------------
--          Node Properties and Tag Resolution
--------------------------------------------------------------------------------

||| The properties of a node: at most one anchor and one tag
||| [spec: c-ns-properties].
public export
record Props where
  constructor MkProps
  anchor : Maybe Anchor
  tag    : Tag

public export
noProps : Props
noProps = MkProps Nothing NoTag

public export
isNoProps : Props -> Bool
isNoProps (MkProps Nothing NoTag) = True
isNoProps _                       = False

||| The tag handles declared by `%TAG` directives; `!` and `!!` have
||| built-in defaults.
public export
record TagEnv where
  constructor TE
  handles : List (String, String)

public export
defaultEnv : TagEnv
defaultEnv = TE []

--------------------------------------------------------------------------------
--          Errors
--------------------------------------------------------------------------------

||| YAML-specific parse errors, used as the custom part of
||| `InnerError` (see `Text.ParseError`).
public export
data YErr : Type where
  TabIndent       : YErr
  BadIndent       : YErr
  MultipleAnchors : YErr
  MultipleTags    : YErr
  UnknownHandle   : String -> YErr
  DuplicateHandle : String -> YErr
  BadVersion      : String -> YErr
  BadDirective    : String -> YErr
  TrailingContent : YErr
  InvalidKey      : YErr

  -- composer errors

  ||| An alias referencing an anchor that is not in scope.
  UndefinedAlias  : Anchor -> YErr

  ||| An alias referencing an anchor whose node is still being
  ||| composed, as in `&a [*a]`: such cyclic structures cannot be
  ||| represented as finite trees.
  CyclicAlias     : Anchor -> YErr

  ||| A mapping with two equal keys [spec 3.2.1.3]. Carries the
  ||| rendered key.
  DuplicateKey    : String -> YErr

  ||| The composer met a malformed event sequence. Event streams
  ||| produced by `parseEvents` never trigger this. Carries the
  ||| rendered event.
  UnexpectedEvent : String -> YErr

  ||| The events ended in the middle of a node or document.
  UnexpectedEnd   : YErr

%runElab derive "YErr" [Show,Eq]

||| Resolves a tag shorthand against the active handles
||| [spec: c-ns-shorthand-tag].
export
resolveTag : TagEnv -> (handle, suffix : String) -> Either YErr Tag
resolveTag env h sfx = case lookup h env.handles of
  Just pre => Right (Verbatim (pre ++ sfx))
  Nothing  => case h of
    "!"  => Right (Verbatim ("!" ++ sfx))
    "!!" => Right (Verbatim ("tag:yaml.org,2002:" ++ sfx))
    _    => Left (UnknownHandle h)

||| Combines properties given on a preceding line with those attached
||| directly to a node: at most one anchor and one tag in total.
export
mergeProps : Props -> Props -> Either YErr Props
mergeProps (MkProps (Just _) _) (MkProps (Just _) _) = Left MultipleAnchors
mergeProps (MkProps a1 NoTag) (MkProps a2 t)         = Right (MkProps (a1 <|> a2) t)
mergeProps (MkProps a1 t) (MkProps a2 NoTag)         = Right (MkProps (a1 <|> a2) t)
mergeProps _ _                                       = Left MultipleTags

export
Interpolation YErr where
  interpolate TabIndent           = "tab character used for indentation"
  interpolate BadIndent           = "wrong indentation"
  interpolate MultipleAnchors     = "more than one anchor for the same node"
  interpolate MultipleTags        = "more than one tag for the same node"
  interpolate (UnknownHandle h)   = "unknown tag handle: \{h}"
  interpolate (DuplicateHandle h) = "duplicate tag handle: \{h}"
  interpolate (BadVersion v)      = "unsupported YAML version: \{v}"
  interpolate (BadDirective d)    = "invalid directive: \{d}"
  interpolate TrailingContent     = "content not allowed after document end"
  interpolate InvalidKey          = "invalid mapping key"
  interpolate (UndefinedAlias a)  = "undefined alias: *\{a}"
  interpolate (CyclicAlias a)     = "alias *\{a} refers to its own ancestor"
  interpolate (DuplicateKey k)    = "duplicate mapping key: \{k}"
  interpolate (UnexpectedEvent e) = "unexpected event: \{e}"
  interpolate UnexpectedEnd       = "unexpected end of events"
