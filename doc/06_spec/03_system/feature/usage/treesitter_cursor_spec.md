# TreeSitter Heuristic Mode Specification

> use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TreeSitter Heuristic Mode Specification

use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-CURSOR-001 to #TS-CURSOR-015 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/03_system/feature/usage/treesitter_cursor_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## API

```simple
use std.spec.step

use compiler.treesitter.*
use compiler.core.lexer.*

# Create heuristic-mode parser
var ts = TreeSitter(
lexer: lexer_new(source),
current: lex_token_eof(1),
previous: lex_token_eof(1),
errors: [],
doc_comment: nil,
inline_blocks: [],
current_context: nil,
fast_mode: false,
heuristic_mode: true,
registry: nil
)
val outline = ts.parse_outline()
```

## Scenarios

### Heuristic Function Parsing

#### parses fn declaration

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses fn declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses fn declaration")
val source = "fn hello():\n    42"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
```

</details>

#### parses multiple functions

- parses multiple functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses multiple functions")
val source = "fn foo():\n    1\nfn bar():\n    2"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 2
```

</details>

### Heuristic Class Parsing

#### parses class declaration

- parses class declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses class declaration")
val source = "class Point:\n    x: i64\n    y: i64"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.classes.len() to_equal 1
```

</details>

### Heuristic Struct Parsing

#### parses struct declaration

- parses struct declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses struct declaration")
val source = "struct Vec2:\n    x: f64\n    y: f64"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.structs.len() to_equal 1
```

</details>

### Heuristic Enum Parsing

#### parses enum declaration

- parses enum declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses enum declaration")
val source = "enum Color:\n    Red\n    Green\n    Blue"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.enums.len() to_equal 1
```

</details>

### Heuristic Trait Parsing

#### parses trait declaration

- parses trait declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses trait declaration")
val source = "trait Drawable:\n    fn draw():\n        pass"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.traits.len() to_equal 1
```

</details>

### Heuristic Impl Parsing

#### parses impl block

- parses impl block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses impl block")
val source = "impl Point:\n    fn get_x() -> i64:\n        self.x"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.impls.len() to_equal 1
```

</details>

#### parses impl with multiple members

- parses impl with multiple members


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses impl with multiple members")
val source = "impl Point:\n    fn get_x() -> i64:\n        self.x\n    fn get_y() -> i64:\n        self.y"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.impls.len() to_equal 1
# Methods inside impl are collected separately as functions
expect outline.functions.len() >= 2
```

</details>

### Heuristic Visibility Detection

#### detects pub function

- detects pub function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects pub function")
val source = "pub fn hello():\n    42"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 1
```

</details>

#### detects pub struct

- detects pub struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects pub struct")
val source = "pub struct Point:\n    x: i64"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.structs.len() to_equal 1
```

</details>

### Heuristic Error Tolerance

#### handles empty source

- handles empty source


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty source")
val source = ""
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 0
```

</details>

#### skips unrecognized lines

- skips unrecognized lines


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("skips unrecognized lines")
val source = "some random text\nfn valid():\n    42"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
# Should still find the valid function
expect outline.functions.len() to_equal 1
```

</details>

#### parses mixed valid and invalid

- parses mixed valid and invalid


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses mixed valid and invalid")
val source = "fn first():\n    1\n??? invalid ???\nfn second():\n    2"
var ts = make_heuristic_ts(source)
val outline = ts.parse_outline()
expect outline.functions.len() to_equal 2
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `407e891e231f28af4d1b28ad088f787eb4cc82db16f1a13ffa52ef5dedcf1dd8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `407e891e231f28af4d1b28ad088f787eb4cc82db16f1a13ffa52ef5dedcf1dd8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `407e891e231f28af4d1b28ad088f787eb4cc82db16f1a13ffa52ef5dedcf1dd8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/treesitter_cursor_spec.spl
mirror: doc/06_spec/03_system/feature/usage/treesitter_cursor_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/treesitter_cursor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/treesitter_cursor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/treesitter_cursor_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses fn declaration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/treesitter_cursor_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses multiple functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/treesitter_cursor_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses class declaration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
