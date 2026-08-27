# TreeSitter Parser Specification

> use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TreeSitter Parser Specification

use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-PARSER-001 to #TS-PARSER-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/treesitter_parser_spec.spl` |
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

### TreeSitter Parser Creation

#### creates parser from source

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates parser from source


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates parser from source")
var ts = TreeSitter.new("val x = 42")
val outline = ts.parse_outline()
# Parser created and parsed without crashing
expect true to_equal true
```

</details>

#### creates parser from empty source

- creates parser from empty source


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates parser from empty source")
var ts = TreeSitter.new("")
val outline = ts.parse_outline()
expect true to_equal true
```

</details>

### TreeSitter Basic Function Parsing

#### parses single function

- parses single function


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses single function")
val source = "fn test():\n    42"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
expect outline.functions[0].name to_equal "test"
```

</details>

#### parses function with return type

- parses function with return type


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses function with return type")
val source = "fn get_value() -> i64:\n    42"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
val f = outline.functions[0]
expect f.name to_equal "get_value"
expect f.has_return_type to_equal true
```

</details>

#### parses function with parameters

- parses function with parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses function with parameters")
val source = "fn greet(name: text) -> text:\n    name"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
val f = outline.functions[0]
expect f.params.len() to_equal 1
```

</details>

### TreeSitter Basic Struct Parsing

#### parses struct with fields

- parses struct with fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses struct with fields")
val source = "struct Point:\n    x: i64\n    y: i64"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.structs.len() to_equal 1
val s = outline.structs[0]
expect s.name to_equal "Point"
expect s.fields.len() to_equal 2
```

</details>

### TreeSitter Basic Enum Parsing

#### parses enum with variants

- parses enum with variants


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses enum with variants")
val source = "enum Direction:\n    North\n    South\n    East\n    West"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.enums.len() to_equal 1
val e = outline.enums[0]
expect e.name to_equal "Direction"
expect e.variants.len() to_equal 4
```

</details>

### TreeSitter Import Parsing

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

### TreeSitter Export Parsing

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

### TreeSitter Multi-Declaration Parsing

#### parses function and struct

- parses function and struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses function and struct")
val source = "fn hello():\n    42\n\nstruct Point:\n    x: i64\n    y: i64"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
expect outline.structs.len() to_equal 1
```

</details>

#### parses function, struct, and enum

- parses function, struct, and enum


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses function, struct, and enum")
val source = "fn hello():\n    42\n\nstruct Point:\n    x: i64\n\nenum Color:\n    Red\n    Blue"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
expect outline.structs.len() to_equal 1
expect outline.enums.len() to_equal 1
```

</details>

### TreeSitter Complex Source Parsing

#### parses function with impl

- parses function with impl


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses function with impl")
val source = "struct Point:\n    x: i64\n    y: i64\n\nimpl Point:\n    fn get_x() -> i64:\n        self.x"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.structs.len() to_equal 1
expect outline.impls.len() to_equal 1
```

</details>

### TreeSitter Empty Source Parsing

#### returns empty outline for empty source

- returns empty outline for empty source


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns empty outline for empty source")
var ts = TreeSitter.new("")
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 0
expect outline.classes.len() to_equal 0
expect outline.structs.len() to_equal 0
expect outline.enums.len() to_equal 0
expect outline.traits.len() to_equal 0
expect outline.impls.len() to_equal 0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `9ac876360a58eae12aced0b71963421224a8aac89f2d127338501cc32390e83b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9ac876360a58eae12aced0b71963421224a8aac89f2d127338501cc32390e83b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9ac876360a58eae12aced0b71963421224a8aac89f2d127338501cc32390e83b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/treesitter_parser_spec.spl
mirror: doc/06_spec/feature/usage/treesitter_parser_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/treesitter_parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/treesitter_parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/treesitter_parser_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates parser from source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/treesitter_parser_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates parser from empty source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/treesitter_parser_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses single function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
