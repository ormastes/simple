# TreeSitter OutlineModule Structure Specification

> use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TreeSitter OutlineModule Structure Specification

use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-TREE-001 to #TS-TREE-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/treesitter_tree_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## API

```simple
use std.spec.step

use compiler.treesitter.*

var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
```

## Scenarios

### OutlineModule Function Parsing

#### parses a simple function

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses a simple function


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses a simple function")
val source = "fn hello():\n    42"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
val f = outline.functions[0]
expect f.name to_equal "hello"
```

</details>

#### parses function with parameters

- parses function with parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses function with parameters")
val source = "fn add(x: i64, y: i64) -> i64:\n    x + y"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
val f = outline.functions[0]
expect f.name to_equal "add"
expect f.params.len() to_equal 2
```

</details>

#### parses extern function

- parses extern function


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses extern function")
val source = "extern fn rt_read(path: text) -> text"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
val f = outline.functions[0]
expect f.name to_equal "rt_read"
expect f.is_extern to_equal true
```

</details>

#### parses multiple functions

- parses multiple functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses multiple functions")
val source = "fn foo():\n    1\n\nfn bar():\n    2\n\nfn baz():\n    3"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 3
```

</details>

### OutlineModule Class Parsing

#### parses a simple class

- parses a simple class


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses a simple class")
val source = "class Point:\n    x: i64\n    y: i64"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.classes.len() to_equal 1
val c = outline.classes[0]
expect c.name to_equal "Point"
```

</details>

#### parses class fields

- parses class fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses class fields")
val source = "class Point:\n    x: i64\n    y: i64"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
val c = outline.classes[0]
expect c.fields.len() to_equal 2
```

</details>

### OutlineModule Struct Parsing

#### parses a simple struct

- parses a simple struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses a simple struct")
val source = "struct Vec2:\n    x: f64\n    y: f64"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.structs.len() to_equal 1
val s = outline.structs[0]
expect s.name to_equal "Vec2"
```

</details>

#### parses struct fields

- parses struct fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses struct fields")
val source = "struct Color:\n    r: u8\n    g: u8\n    b: u8"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
val s = outline.structs[0]
expect s.fields.len() to_equal 3
```

</details>

### OutlineModule Enum Parsing

#### parses a simple enum

- parses a simple enum


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses a simple enum")
val source = "enum Color:\n    Red\n    Green\n    Blue"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.enums.len() to_equal 1
val e = outline.enums[0]
expect e.name to_equal "Color"
```

</details>

#### parses enum variants

- parses enum variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses enum variants")
val source = "enum Direction:\n    North\n    South\n    East\n    West"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
val e = outline.enums[0]
expect e.variants.len() to_equal 4
```

</details>

### OutlineModule Import Parsing

#### parses use statement

- parses use statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses use statement")
val source = "use std.text.{NL2}\n\nfn main():\n    42"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.imports.len() >= 1
```

</details>

#### parses export statement

- parses export statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses export statement")
val source = "export Foo, Bar"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.exports.len() to_equal 1
```

</details>

### OutlineModule Multiple Declarations

#### parses mixed declarations

- parses mixed declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses mixed declarations")
val source = "fn hello():\n    42\n\nstruct Point:\n    x: i64\n    y: i64\n\nenum Color:\n    Red\n    Blue"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
expect outline.structs.len() to_equal 1
expect outline.enums.len() to_equal 1
```

</details>

#### produces empty module for empty source

- produces empty module for empty source


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("produces empty module for empty source")
val source = ""
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 0
expect outline.classes.len() to_equal 0
expect outline.structs.len() to_equal 0
expect outline.enums.len() to_equal 0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `176e4a6d6d251c3734f11ab9f3de4f557e0e601ba0a8c6c6326e79a9fad4a6a0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `176e4a6d6d251c3734f11ab9f3de4f557e0e601ba0a8c6c6326e79a9fad4a6a0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `176e4a6d6d251c3734f11ab9f3de4f557e0e601ba0a8c6c6326e79a9fad4a6a0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/treesitter_tree_spec.spl
mirror: doc/06_spec/feature/usage/treesitter_tree_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/treesitter_tree_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/treesitter_tree_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/treesitter_tree_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a simple function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/treesitter_tree_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses function with parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/treesitter_tree_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses extern function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
