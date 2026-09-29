# Branch Coverage 35 Specification

> Tests covering Functions Returning Optional, Optional in Expressions, Type Inference for Optionals, Long Type Names, Nested Optional Types, Optional Struct Fields, Optional in Collections, Type Base Extraction.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Branch Coverage 35 Specification

## Scenarios

### Functions Returning Optional

#### function with optional return

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- function with optional return


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function with optional return")
fn maybe_value() -> i64?:
    Some(42)

val result = maybe_value()
check(result.?)
```

</details>

#### function returning nil

- function returning nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function returning nil")
fn get_none() -> i64?:
    nil

val result = get_none()
check(not result.?)
```

</details>

#### conditional optional return

- conditional optional return


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("conditional optional return")
fn conditional(flag: bool) -> i64?:
    if flag:
        return Some(100)
    nil

check(conditional(true).?)
check(not conditional(false).?)
```

</details>

### Optional in Expressions

#### optional function in if

- optional function in if


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional function in if")
fn maybe_positive() -> i64?:
    Some(5)

if maybe_positive().?:
    check(true)
else:
    check(false)
```

</details>

#### optional with default

- optional with default


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional with default")
fn might_fail() -> i64?:
    nil

val value = might_fail() ?? 99
check(value == 99)
```

</details>

#### optional coalesce with value

- optional coalesce with value


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional coalesce with value")
fn get_optional() -> i64?:
    Some(10)

val result = get_optional() ?? 0
check(result == 10)
```

</details>

### Type Inference for Optionals

#### infer from Some

- infer from Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer from Some")
val x = Some(42)
check(x.?)
```

</details>

#### infer from nil

- infer from nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer from nil")
val n: i64? = nil
check(not n.?)
```

</details>

#### infer from function

- infer from function


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("infer from function")
fn returns_opt() -> text?:
    Some("hello")

val s = returns_opt()
check(s.?)
```

</details>

### Long Type Names

#### struct with long name

- struct with long name


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("struct with long name")
struct VeryLongStructNameForTestingBufferLimits:
    value: i64

val item = VeryLongStructNameForTestingBufferLimits(value: 42)
check(item.value == 42)
```

</details>

#### optional of long struct

- optional of long struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional of long struct")
struct AnotherVeryLongNameToTestOptionalHandling:
    id: i64

val opt: AnotherVeryLongNameToTestOptionalHandling? = nil
check(not opt.?)
```

</details>

### Nested Optional Types

#### optional of optional

- optional of optional


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional of optional")
val o1 = Some(Some(42))
check(o1.?)
```

</details>

#### optional of optional - nil inner

- optional of optional - nil inner


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional of optional - nil inner")
val o2 = Some(nil)
check(o2.?)
```

</details>

#### function returning nested optional

- function returning nested optional


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function returning nested optional")
fn nested_opt() -> i64?:
    Some(100)

val result = nested_opt()
check(result.?)
```

</details>

### Optional Struct Fields

#### struct with optional field

- struct with optional field


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("struct with optional field")
struct Record:
    id: i64
    optional_value: i64?

val r1 = Record(id: 1, optional_value: Some(10))
val r2 = Record(id: 2, optional_value: nil)

check(r1.optional_value.?)
check(not r2.optional_value.?)
```

</details>

### Optional in Collections

#### array of optionals

- array of optionals


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array of optionals")
val arr = [Some(1), nil, Some(3)]
check(arr[0].?)
check(not arr[1].?)
```

</details>

#### optional array

- optional array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional array")
val opt_arr = Some([1, 2, 3])
check(opt_arr.?)
```

</details>

### Type Base Extraction

#### non-optional type

- non-optional type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-optional type")
val y: i64 = 42
check(y == 42)
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
val s: text = "hello"
check(s == "hello")
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
val b: bool = true
check(b)
```

</details>

#### optional extract via coalesce

- optional extract via coalesce


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional extract via coalesce")
val x: i64? = Some(42)
val unwrapped = x ?? 0
check(unwrapped == 42)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler_core/branch_coverage_35_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Functions Returning Optional, Optional in Expressions, Type Inference for Optionals, Long Type Names, Nested Optional Types, Optional Struct Fields, Optional in Collections, Type Base Extraction.
- Functions Returning Optional
- Optional in Expressions
- Type Inference for Optionals
- Long Type Names
- Nested Optional Types
- Optional Struct Fields
- Optional in Collections
- Type Base Extraction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `e649aff719a708028473fe2c2b8746a9cfcd234b6dbaab2c534cd2367119e237`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e649aff719a708028473fe2c2b8746a9cfcd234b6dbaab2c534cd2367119e237`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e649aff719a708028473fe2c2b8746a9cfcd234b6dbaab2c534cd2367119e237`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler_core/branch_coverage_35_spec.spl
mirror: doc/06_spec/unit/compiler_core/branch_coverage_35_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler_core/branch_coverage_35_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler_core/branch_coverage_35_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler_core/branch_coverage_35_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'function with optional return' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/branch_coverage_35_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'function returning nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/branch_coverage_35_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'conditional optional return' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
