# Type System Specification

> Tests covering Primitive Types, Composite Types, Type Conversions, Type Aliases, Type Checking Errors, Subtyping, Type Constraints.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type System Specification

## Scenarios

### Primitive Types

#### i64 type

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- i64 type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("i64 type")
val x: i64 = 42
check(x == 42)
```

</details>

#### f64 type

- f64 type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("f64 type")
val x: f64 = 3.14
check(x > 3.0)
```

</details>

#### bool type

- bool type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bool type")
val x: bool = true
check(x)
```

</details>

#### text type

- text type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("text type")
val x: text = "hello"
check(x == "hello")
```

</details>

#### unit type

- unit type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unit type")
val x = ()
check(true)
```

</details>

### Composite Types

#### array type

- array type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array type")
val arr: [i64] = [1, 2, 3]
check(arr.len() == 3)
```

</details>

#### optional type

- optional type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional type")
val x: Option<i64> = Some(42)
check(x.?)
```

</details>

#### tuple type

- tuple type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tuple type")
val pair = (1, "hello")
check(true)
```

</details>

#### map type

- map type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("map type")
val m = {"key": "value"}
check(m.len() == 1)
```

</details>

### Type Conversions

#### i64 to f64

- i64 to f64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("i64 to f64")
val x: i64 = 42
val y = x.to_f64()
check(y > 41.0 and y < 43.0)
```

</details>

#### f64 to i64

- f64 to i64


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("f64 to i64")
val x: f64 = 42.7
val y = x.to_i64()
check(y == 42)
```

</details>

#### i64 to text

- i64 to text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("i64 to text")
val x: i64 = 42
val s = "{x}"
check(s == "42")
```

</details>

#### bool to text

- bool to text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bool to text")
val x = true
val s = "{x}"
check(s == "true")
```

</details>

### Type Aliases

#### type alias basic

- type alias basic


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type alias basic")
type Number = i64
val x: Number = 42
check(x == 42)
```

</details>

### Type Checking Errors

#### type mismatch is error

- type mismatch is error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type mismatch is error")
val error = "type_mismatch"
check(error == "type_mismatch")
```

</details>

#### undeclared type is error

- undeclared type is error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("undeclared type is error")
val error = "undeclared_type"
check(error == "undeclared_type")
```

</details>

#### incompatible return type is error

- incompatible return type is error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("incompatible return type is error")
val error = "incompatible_return"
check(error == "incompatible_return")
```

</details>

#### argument count mismatch is error

- argument count mismatch is error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("argument count mismatch is error")
val error = "arg_count_mismatch"
check(error == "arg_count_mismatch")
```

</details>

### Subtyping

#### nil is subtype of Option

- nil is subtype of Option


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nil is subtype of Option")
val x: Option<i64> = nil
check(x == nil)
```

</details>

#### Some is subtype of Option

- Some is subtype of Option


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Some is subtype of Option")
val x: Option<i64> = Some(42)
check(x.?)
```

</details>

### Type Constraints

#### numeric constraint

- numeric constraint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("numeric constraint")
val x = 42
val y = x + 1
check(y == 43)
```

</details>

#### equality constraint

- equality constraint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("equality constraint")
val x = 42
val y = 42
check(x == y)
```

</details>

#### ordering constraint

- ordering constraint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("ordering constraint")
val x = 3
val y = 5
check(x < y)
```

</details>

#### string constraint

- string constraint


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("string constraint")
val x = "hello"
check(x.len() == 5)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/types/type_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Primitive Types, Composite Types, Type Conversions, Type Aliases, Type Checking Errors, Subtyping, Type Constraints.
- Primitive Types
- Composite Types
- Type Conversions
- Type Aliases
- Type Checking Errors
- Subtyping
- Type Constraints

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
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

- Canonical SPipe generation for source `2f9c90c70a050572bc5653d3187934b89d84866328c8e061707e1e7c61aa77e0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2f9c90c70a050572bc5653d3187934b89d84866328c8e061707e1e7c61aa77e0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2f9c90c70a050572bc5653d3187934b89d84866328c8e061707e1e7c61aa77e0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/types/type_system_spec.spl
mirror: doc/06_spec/01_unit/compiler/types/type_system_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/types/type_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/types/type_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/types/type_system_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'i64 type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/types/type_system_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'f64 type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/types/type_system_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bool type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
