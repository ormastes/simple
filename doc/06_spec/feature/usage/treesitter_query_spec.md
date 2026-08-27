# TreeSitter Advanced Outline Parsing Specification

> use std.spec.step

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TreeSitter Advanced Outline Parsing Specification

use std.spec.step

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #TS-QUERY-001 to #TS-QUERY-020 |
| Category | Infrastructure \| Parser |
| Status | Implemented |
| Source | `test/feature/usage/treesitter_query_spec.spl` |
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

### OutlineModule Type Parameters

#### parses struct with type parameter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses struct with type parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses struct with type parameter")
val source = "struct Box<T>:\n    value: T"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.structs.len() to_equal 1
val s = outline.structs[0]
expect s.name to_equal "Box"
expect s.type_params.len() to_equal 1
```

</details>

#### parses class with multiple type parameters

- parses class with multiple type parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses class with multiple type parameters")
val source = "class Pair<A, B>:\n    first: A\n    second: B"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.classes.len() to_equal 1
val c = outline.classes[0]
expect c.name to_equal "Pair"
expect c.type_params.len() to_equal 2
```

</details>

### OutlineModule Trait Parsing

#### parses trait with methods

- parses trait with methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses trait with methods")
val source = "trait Drawable:\n    fn draw():\n        pass\n    fn area() -> f64:\n        0.0"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.traits.len() to_equal 1
val t = outline.traits[0]
expect t.name to_equal "Drawable"
```

</details>

#### parses empty trait

- parses empty trait


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses empty trait")
val source = "trait Marker:\n    pass"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.traits.len() to_equal 1
val t = outline.traits[0]
expect t.name to_equal "Marker"
```

</details>

### OutlineModule Impl Parsing

#### parses impl with methods

- parses impl with methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses impl with methods")
val source = "impl Point:\n    fn get_x() -> i64:\n        self.x\n    fn get_y() -> i64:\n        self.y"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.impls.len() to_equal 1
```

</details>

#### parses impl with static method

- parses impl with static method


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses impl with static method")
val source = "impl Point:\n    static fn origin() -> Point:\n        Point(x: 0, y: 0)"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.impls.len() to_equal 1
```

</details>

### OutlineModule Type Alias Parsing

#### parses type alias

- parses type alias


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses type alias")
val source = "type Point2D = Point"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.type_aliases.len() to_equal 1
val ta = outline.type_aliases[0]
expect ta.name to_equal "Point2D"
```

</details>

### OutlineModule Const Parsing

#### parses val declaration

- parses val declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses val declaration")
val source = "val PI = 3.14"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.constants.len() to_equal 1
val c = outline.constants[0]
expect c.name to_equal "PI"
expect c.is_mutable to_equal false
```

</details>

#### parses var declaration

- parses var declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses var declaration")
val source = "var counter = 0"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.constants.len() to_equal 1
val c = outline.constants[0]
expect c.name to_equal "counter"
expect c.is_mutable to_equal true
```

</details>

### OutlineModule Mixed Advanced Declarations

#### parses traits and impls together

- parses traits and impls together


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses traits and impls together")
val source = "trait Shape:\n    fn area() -> f64:\n        0.0\n\nimpl Circle:\n    fn area() -> f64:\n        3.14"
var ts = TreeSitter.new(source)
val outline = ts.parse_outline()
expect outline.traits.len() to_equal 1
expect outline.impls.len() to_equal 1
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `e9568d5626e7372cab823ad8ea8584900aa57202122b8d575093def1f7e6403b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e9568d5626e7372cab823ad8ea8584900aa57202122b8d575093def1f7e6403b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e9568d5626e7372cab823ad8ea8584900aa57202122b8d575093def1f7e6403b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/treesitter_query_spec.spl
mirror: doc/06_spec/feature/usage/treesitter_query_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/treesitter_query_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/treesitter_query_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/treesitter_query_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses struct with type parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/treesitter_query_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses class with multiple type parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/treesitter_query_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses trait with methods' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
