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

```idris
import Text.YAML

parse : String -> Either (ParseError YErr) (List Event)
parse = parseEvents Virtual
```

`Event` mirrors the YAML processing model's parse events
(`StreamStart`, `DocStart`, `SeqStart`, `MapStart`, `Scalar`, `Alias`,
and their ends). `printEvent` renders an event in the format used by
the test suite's `test.event` files. A composer building node trees
from the event stream may be added in the future.

## Building and testing

This is a [pack](https://github.com/stefan-hoeck/idris2-pack) project:

```sh
pack install yaml
pack test yaml
```

The test executable runs the vendored test suite snapshot under
`test/suite` (upstream commit recorded in `test/suite/COMMIT`)
followed by a group of hedgehog properties.
