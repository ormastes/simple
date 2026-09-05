# Static Constants Specification

> Tests covering static constant desugaring.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static Constants Specification

## Scenarios

### static constant desugaring

#### extracts simple static val from impl block

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts simple static val from impl block
   - Expected: kept_impl is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts simple static val from impl block")
val input = "impl Point:\n    static val ORIGIN = Point(x: 0, y: 0)"
val output = desugar_static_constants(input)

expect(output).to_contain("val Point__ORIGIN = Point(x: 0, y: 0)")
# This impl block held nothing but the static constant, so the block is
# dropped once the constant is hoisted -- the same rule the
# "removes impl block if only static constants remain" example asserts.
# The original `to_contain("impl Point:")` here contradicted that rule
# and was never true: the emit-header guard `if remaining_decls.len() > 0`
# is present in the module's first revision, 97a9358145f (2026-07-01).
val kept_impl = output.contains("impl Point:")
expect(kept_impl).to_equal(false)
```

</details>

#### extracts multiple static constants

- extracts multiple static constants


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts multiple static constants")
val input = "impl Config:\n    static val MAX_SIZE = 1000\n    static val MIN_SIZE = 10"
val output = desugar_static_constants(input)

expect(output).to_contain("val Config__MAX_SIZE = 1000")
expect(output).to_contain("val Config__MIN_SIZE = 10")
```

</details>

#### preserves instance methods when extracting constants

- preserves instance methods when extracting constants


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves instance methods when extracting constants")
val input = "impl Point:\n    static val ORIGIN = Point(x: 0, y: 0)\n    fn distance() -> f64:\n        0.0"
val output = desugar_static_constants(input)

expect(output).to_contain("val Point__ORIGIN")
expect(output).to_contain("impl Point:")
expect(output).to_contain("fn distance() -> f64:")
```

</details>

#### preserves static methods when extracting constants

- preserves static methods when extracting constants


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves static methods when extracting constants")
val input = "impl Point:\n    static val ORIGIN = Point(x: 0, y: 0)\n    static fn new(x: i64, y: i64) -> Point:\n        Point(x: x, y: y)"
val output = desugar_static_constants(input)

expect(output).to_contain("val Point__ORIGIN")
expect(output).to_contain("static fn new(x: i64, y: i64)")
```

</details>

#### handles static var as constant

- handles static var as constant


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles static var as constant")
val input = "impl Counter:\n    static var instance_count = 0"
val output = desugar_static_constants(input)

expect(output).to_contain("val Counter__instance_count = 0")
```

</details>

#### handles constants with type annotations

- handles constants with type annotations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles constants with type annotations")
val input = "impl Math:\n    static val PI: f64 = 3.14159"
val output = desugar_static_constants(input)

expect(output).to_contain("val Math__PI: f64 = 3.14159")
```

</details>

#### handles constants with uppercase names

- handles constants with uppercase names


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles constants with uppercase names")
val input = "impl Color:\n    static val RED = 0xFF0000\n    static val GREEN = 0x00FF00\n    static val BLUE = 0x0000FF"
val output = desugar_static_constants(input)

expect(output).to_contain("val Color__RED = 0xFF0000")
expect(output).to_contain("val Color__GREEN = 0x00FF00")
expect(output).to_contain("val Color__BLUE = 0x0000FF")
```

</details>

#### handles constants with mixed case names

- handles constants with mixed case names


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles constants with mixed case names")
val input = "impl Config:\n    static val default_timeout = 30\n    static val MAX_RETRIES = 3"
val output = desugar_static_constants(input)

expect(output).to_contain("val Config__default_timeout = 30")
expect(output).to_contain("val Config__MAX_RETRIES = 3")
```

</details>

#### preserves impl block structure with mixed content

- preserves impl block structure with mixed content


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves impl block structure with mixed content")
val input = "impl Point:\n    static val ZERO = 0\n    fn get_x() -> i64:\n        self.x\n    static val ONE = 1\n    fn get_y() -> i64:\n        self.y"
val output = desugar_static_constants(input)

expect(output).to_contain("val Point__ZERO = 0")
expect(output).to_contain("val Point__ONE = 1")
expect(output).to_contain("impl Point:")
expect(output).to_contain("fn get_x()")
expect(output).to_contain("fn get_y()")
```

</details>

#### handles impl blocks with no static constants

- handles impl blocks with no static constants
   - Expected: output equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles impl blocks with no static constants")
val input = "impl Point:\n    fn distance() -> f64:\n        0.0"
val output = desugar_static_constants(input)

expect(output).to_equal(input)
```

</details>

#### handles empty impl blocks

- handles empty impl blocks
   - Expected: output equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty impl blocks")
val input = "impl Empty:\n    pass"
val output = desugar_static_constants(input)

expect(output).to_equal(input)
```

</details>

#### handles multiple impl blocks

- handles multiple impl blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple impl blocks")
val input = "impl Point:\n    static val ORIGIN = Point(0, 0)\n\nimpl Color:\n    static val RED = 0xFF0000"
val output = desugar_static_constants(input)

expect(output).to_contain("val Point__ORIGIN")
expect(output).to_contain("val Color__RED")
```

</details>

#### handles impl blocks with trait implementations

- handles impl blocks with trait implementations


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles impl blocks with trait implementations")
# Braces doubled so this spec's own literal is not interpolated; `input`
# still holds the intended single-brace text `"({x}, {y})"`.
val input = "impl Display for Point:\n    static val FORMAT = \"({{x}}, {{y}})\"\n    fn to_string() -> text:\n        \"point\""
val output = desugar_static_constants(input)

expect(output).to_contain("val Point__FORMAT")
expect(output).to_contain("impl Display for Point:")
expect(output).to_contain("fn to_string()")
```

</details>

#### handles impl blocks with generic type parameters

- handles impl blocks with generic type parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles impl blocks with generic type parameters")
val input = "impl Option<T>:\n    static val NONE_SENTINEL = -1"
val output = desugar_static_constants(input)

expect(output).to_contain("val Option__NONE_SENTINEL = -1")
```

</details>

#### removes impl block if only static constants remain

- removes impl block if only static constants remain
   - Expected: has_empty_impl is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes impl block if only static constants remain")
val input = "impl Constants:\n    static val A = 1\n    static val B = 2"
val output = desugar_static_constants(input)

expect(output).to_contain("val Constants__A = 1")
expect(output).to_contain("val Constants__B = 2")
# The impl block should be removed since it's now empty
val lines = output.split("\n")
var has_empty_impl = false
for line in lines:
    if line.trim() == "impl Constants:":
        has_empty_impl = true
expect(has_empty_impl).to_equal(false)
```

</details>

#### handles constants with complex expressions

- handles constants with complex expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles constants with complex expressions")
val input = "impl Math:\n    static val TAU = 2.0 * 3.14159"
val output = desugar_static_constants(input)

expect(output).to_contain("val Math__TAU = 2.0 * 3.14159")
```

</details>

#### handles constants with constructor calls

- handles constants with constructor calls


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles constants with constructor calls")
val input = "impl Point:\n    static val UNIT_X = Point(x: 1, y: 0)\n    static val UNIT_Y = Point(x: 0, y: 1)"
val output = desugar_static_constants(input)

expect(output).to_contain("val Point__UNIT_X = Point(x: 1, y: 0)")
expect(output).to_contain("val Point__UNIT_Y = Point(x: 0, y: 1)")
```

</details>

#### handles constants with array values

- handles constants with array values


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles constants with array values")
val input = "impl Defaults:\n    static val EMPTY_LIST = []"
val output = desugar_static_constants(input)

expect(output).to_contain("val Defaults__EMPTY_LIST = []")
```

</details>

#### handles constants with string values

- handles constants with string values


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles constants with string values")
val input = "impl Messages:\n    static val GREETING = \"Hello, World!\""
val output = desugar_static_constants(input)

expect(output).to_contain("val Messages__GREETING = \"Hello, World!\"")
```

</details>

#### preserves indentation for module-level constants

- preserves indentation for module-level constants
   - Expected: has_leading_space is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves indentation for module-level constants")
val input = "impl Point:\n    static val ORIGIN = Point(x: 0, y: 0)"
val output = desugar_static_constants(input)

# Module-level constants should have no indentation
expect(output).to_contain("val Point__ORIGIN")
val has_leading_space = output.starts_with(" ")
expect(has_leading_space).to_equal(false)
```

</details>

#### handles nested impl blocks correctly

- handles nested impl blocks correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles nested impl blocks correctly")
# NOTE: Simple doesn't support nested impl, but we should handle gracefully
val input = "impl Outer:\n    static val X = 1\n    fn method():\n        impl Inner:\n            static val Y = 2"
val output = desugar_static_constants(input)

# Both constants should be extracted
expect(output).to_contain("val Outer__X = 1")
expect(output).to_contain("val Inner__Y = 2")
```

</details>

#### handles blank lines between static constants

- handles blank lines between static constants


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles blank lines between static constants")
val input = "impl Config:\n    static val A = 1\n\n    static val B = 2"
val output = desugar_static_constants(input)

expect(output).to_contain("val Config__A = 1")
expect(output).to_contain("val Config__B = 2")
```

</details>

#### handles comments before static constants

- handles comments before static constants


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles comments before static constants")
val input = "impl Point:\n    # Origin point\n    static val ORIGIN = Point(0, 0)"
val output = desugar_static_constants(input)

expect(output).to_contain("val Point__ORIGIN")
# Comment should be preserved in impl block
expect(output).to_contain("# Origin point")
```

</details>

#### handles multi-line constant values

- handles multi-line constant values


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multi-line constant values")
val input = "impl Config:\n    static val SETTINGS = Settings(\n        timeout: 30,\n        retries: 3\n    )"
val output = desugar_static_constants(input)

expect(output).to_contain("val Config__SETTINGS = Settings(")
expect(output).to_contain("timeout: 30")
expect(output).to_contain("retries: 3")
```

</details>

#### preserves non-static val declarations

- preserves non-static val declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves non-static val declarations")
val input = "impl Counter:\n    static val MAX = 100\n    val instance_var = 0"
val output = desugar_static_constants(input)

expect(output).to_contain("val Counter__MAX = 100")
expect(output).to_contain("val instance_var = 0")
```

</details>

#### handles constants in impl blocks without methods

- handles constants in impl blocks without methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles constants in impl blocks without methods")
val input = "impl Constants:\n    static val PI = 3.14159\n    static val E = 2.71828"
val output = desugar_static_constants(input)

expect(output).to_contain("val Constants__PI = 3.14159")
expect(output).to_contain("val Constants__E = 2.71828")
```

</details>

#### preserves decorators on impl blocks

- preserves decorators on impl blocks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves decorators on impl blocks")
val input = "@public\nimpl Point:\n    static val ORIGIN = Point(0, 0)"
val output = desugar_static_constants(input)

expect(output).to_contain("val Point__ORIGIN")
expect(output).to_contain("@public")
```

</details>

#### handles underscores in constant names

- handles underscores in constant names


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles underscores in constant names")
val input = "impl Config:\n    static val MAX_BUFFER_SIZE = 4096\n    static val DEFAULT_TIMEOUT_MS = 1000"
val output = desugar_static_constants(input)

expect(output).to_contain("val Config__MAX_BUFFER_SIZE = 4096")
expect(output).to_contain("val Config__DEFAULT_TIMEOUT_MS = 1000")
```

</details>

#### handles numeric constant names correctly

- handles numeric constant names correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles numeric constant names correctly")
val input = "impl Error:\n    static val E404 = \"Not Found\"\n    static val E500 = \"Server Error\""
val output = desugar_static_constants(input)

expect(output).to_contain("val Error__E404")
expect(output).to_contain("val Error__E500")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/desugar/static_constants_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering static constant desugaring.
- static constant desugaring

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b5a2c248d0888cb7ddba23e0c63b4680d04c11689e28f955febc3ac74d597380`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b5a2c248d0888cb7ddba23e0c63b4680d04c11689e28f955febc3ac74d597380`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b5a2c248d0888cb7ddba23e0c63b4680d04c11689e28f955febc3ac74d597380`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/desugar/static_constants_spec.spl
mirror: doc/06_spec/unit/app/desugar/static_constants_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/desugar/static_constants_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/desugar/static_constants_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/desugar/static_constants_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts simple static val from impl block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/desugar/static_constants_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts multiple static constants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/desugar/static_constants_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves instance methods when extracting constants' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
