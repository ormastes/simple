# TreeSitter Error Handling and Edge Cases Specification

> use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TreeSitter Error Handling and Edge Cases Specification

use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-ERR-001 to #TS-ERR-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/usage/treesitter_error_recovery_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## API

```simple
use std.spec.step

use compiler.treesitter.*

var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
# outline.errors contains ParseError items
```

## Scenarios

### TreeSitter Edge Cases - Empty Source

#### produces empty module for empty source

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- produces empty module for empty source


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces empty module for empty source")
var ts = TreeSitter.new("")
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 0
expect outline.classes.len() to_equal 0
expect outline.structs.len() to_equal 0
expect outline.enums.len() to_equal 0
```

</details>

#### produces empty module for whitespace only

- produces empty module for whitespace only


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces empty module for whitespace only")
var ts = TreeSitter.new("   \n   \n   ")
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 0
```

</details>

#### produces empty module for comments only

- produces empty module for comments only


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("produces empty module for comments only")
var ts = TreeSitter.new("# just a comment\n# another comment")
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 0
```

</details>

### TreeSitter Multiple Function Parsing

#### parses three functions

- parses three functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses three functions")
val source = "fn alpha():\n    1\n\nfn beta():\n    2\n\nfn gamma():\n    3"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 3
```

</details>

#### preserves function names

- preserves function names


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves function names")
val source = "fn first():\n    1\n\nfn second():\n    2"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions[0].name to_equal "first"
expect outline.functions[1].name to_equal "second"
```

</details>

### TreeSitter Extern Function Parsing

#### parses extern fn

- parses extern fn


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses extern fn")
val source = "extern fn rt_read(path: text) -> text"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
val f = outline.functions[0]
expect f.name to_equal "rt_read"
expect f.is_extern to_equal true
```

</details>

#### parses extern fn with params

- parses extern fn with params


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses extern fn with params")
val source = "extern fn rt_write(path: text, content: text) -> bool"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
val f = outline.functions[0]
expect f.params.len() to_equal 2
```

</details>

### TreeSitter Method Modifiers

#### parses static method in impl

- parses static method in impl


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses static method in impl")
val source = "impl Point:\n    static fn origin() -> Point:\n        Point(x: 0, y: 0)"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.impls.len() to_equal 1
val impl_block = outline.impls[0]
expect impl_block.methods.len() to_equal 1
val m = impl_block.methods[0]
expect m.is_static to_equal true
```

</details>

#### parses mutable method in impl

- parses mutable method in impl


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses mutable method in impl")
val source = "impl Point:\n    me move(dx: i64):\n        self.x = self.x + dx"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.impls.len() to_equal 1
val impl_block = outline.impls[0]
expect impl_block.methods.len() to_equal 1
val m = impl_block.methods[0]
expect m.is_mutable to_equal true
```

</details>

### TreeSitter Doc Comment Parsing

#### attaches doc comment to function

- attaches doc comment to function


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("attaches doc comment to function")
val source = "## This is a doc comment\nfn hello():\n    42"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
val f = outline.functions[0]
expect f.has_doc_comment to_equal true
```

</details>

#### attaches doc comment to struct

- attaches doc comment to struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("attaches doc comment to struct")
val source = "## A 2D point\nstruct Point:\n    x: i64\n    y: i64"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.structs.len() to_equal 1
val s = outline.structs[0]
expect s.has_doc_comment to_equal true
```

</details>

### TreeSitter Error Recovery

#### continues parsing after valid declarations

- continues parsing after valid declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("continues parsing after valid declarations")
val source = "fn valid_first():\n    1\n\nfn valid_second():\n    2"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 2
```

</details>

#### parses complex source without crashing

- parses complex source without crashing


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses complex source without crashing")
val source = "use std.text.{NL2}\n\nfn main():\n    val x = 42\n    print x\n\nstruct Config:\n    name: text\n    debug: bool"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
# Should find at least the function and struct
expect outline.functions.len() >= 1
```

</details>

### TreeSitter Trait-Impl Parsing

#### parses trait followed by impl

- parses trait followed by impl


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses trait followed by impl")
val source = "trait Greetable:\n    fn greet() -> text:\n        pass\n\nimpl Person:\n    fn greet() -> text:\n        self.name"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.traits.len() to_equal 1
expect outline.impls.len() to_equal 1
```

</details>

#### parses impl methods

- parses impl methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses impl methods")
val source = "impl Calculator:\n    fn add(a: i64, b: i64) -> i64:\n        a + b\n    fn sub(a: i64, b: i64) -> i64:\n        a - b"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
val impl_block = outline.impls[0]
expect impl_block.methods.len() to_equal 2
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `251d22d698fdfa9d77709788dd09d6b22097f94627ae6282058ee240b34eea90`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `251d22d698fdfa9d77709788dd09d6b22097f94627ae6282058ee240b34eea90`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `251d22d698fdfa9d77709788dd09d6b22097f94627ae6282058ee240b34eea90`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/treesitter_error_recovery_spec.spl
mirror: doc/06_spec/03_system/feature/usage/treesitter_error_recovery_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/treesitter_error_recovery_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/treesitter_error_recovery_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/treesitter_error_recovery_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces empty module for empty source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/treesitter_error_recovery_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces empty module for whitespace only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/treesitter_error_recovery_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'produces empty module for comments only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
