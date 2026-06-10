# idris2-yaml

A pure, total YAML 1.2.2 parser for Idris2.

The parser turns a YAML stream into its sequence of parse events,
covering the complete YAML 1.2.2 feature set: block and flow
collections, all five scalar styles, anchors, aliases, tags,
directives and multi-document streams. It passes all 402 cases of the
official [YAML test suite](https://github.com/yaml/yaml-test-suite),
including the 94 cases that must be rejected.

It is largely inspired by
[idris2-parser](https://github.com/stefan-hoeck/idris2-parser) (on
which it depends): a hand-written, single-pass recursive descent
parser whose termination is verified by the totality checker, with no
escape hatches.

## Usage

Most users want the composer, which loads each document of a stream
into a tree of tagged nodes:

```idris
import Text.YAML

docs : String -> Either (ParseError YErr) (List Node)
docs = parseDocs Virtual

port : Node -> Maybe Integer
port doc = lookupKey "port" doc >>= asInteger
```

Composing resolves aliases by substituting the referenced node
(structure is shared, and cyclic references such as `&a [*a]` are
rejected), resolves the tags of untagged nodes against a schema
(`Core` by default; `parseDocsWith` selects `Failsafe` instead), and
rejects mappings with duplicate keys. Scalars keep their raw text and
are interpreted on demand by typed views (`asBool`, `asInteger`,
`asDouble`, `asString`, ...), so an explicitly tagged `!!int abc`
composes fine and only fails on access.

Errors - from the parser and the composer alike - carry source spans
and render as an excerpt of the offending input:

```
Error: alias *a refers to its own ancestor

virtual: 1:5--1:7
 1 | &a [*a]
         ^^
```

One deliberate deviation worth knowing about: node equality (used for
duplicate key detection) compares scalars by tag and raw text, so the
keys `1` and `0x1` are distinct.

The event level is also part of the public API:

```idris
events : String -> Either (ParseError YErr) (List (Bounded Event))
events = parseEvents Virtual
```

`Event` mirrors the YAML processing model's parse events
(`StreamStart`, `DocStart`, `SeqStart`, `MapStart`, `Scalar`, `Alias`,
and their ends), each wrapped with the `Bounds` of the source text it
covers. `printEvent` renders a bare event in the format used by the
test suite's `test.event` files, so a stream prints as
`map (printEvent . val) <$> events s`.

## Building and testing

This is a [pack](https://github.com/stefan-hoeck/idris2-pack) project:

```sh
pack install yaml
pack test yaml
```

The test executable runs the vendored test suite snapshot under
`test/suite` (upstream commit recorded in `test/suite/COMMIT`),
comparing event streams against the suite's `test.event` files and
composed documents against its `in.json` files, followed by groups of
hedgehog properties.
