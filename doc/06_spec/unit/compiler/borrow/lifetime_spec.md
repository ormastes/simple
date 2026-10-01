# Lifetime Specification

> Tests covering Variable Lifetimes, Reference Lifetimes, Drop Ordering, Temporary Lifetimes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lifetime Specification

## Scenarios

### Variable Lifetimes

#### lifetime starts at declaration

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- lifetime starts at declaration


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lifetime starts at declaration")
val x = 42
check(x == 42)
```

</details>

#### lifetime ends at scope exit

- lifetime ends at scope exit


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lifetime ends at scope exit")
var result = 0
if true:
    val temp = 42
    result = temp
check(result == 42)
```

</details>

#### nested lifetimes

- nested lifetimes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested lifetimes")
val outer = 1
if true:
    val middle = 2
    if true:
        val inner = 3
        check(outer + middle + inner == 6)
```

</details>

<details>
<summary>Advanced: loop variable lifetime per iteration</summary>

#### loop variable lifetime per iteration

- loop variable lifetime per iteration


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loop variable lifetime per iteration")
var sum = 0
for i in 0..3:
    val temp = i * 10
    sum = sum + temp
check(sum == 30)
```

</details>


</details>

#### match arm lifetimes

- match arm lifetimes


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match arm lifetimes")
val x = Some(42)
var result = 0
match x:
    Some(v):
        val doubled = v * 2
        result = doubled
    nil:
        result = 0
check(result == 84)
```

</details>

### Reference Lifetimes

#### reference lives within function

- reference lives within function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reference lives within function")
fn get_value() -> i64:
    val x = 42
    x
check(get_value() == 42)
```

</details>

#### return value outlives function

- return value outlives function


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("return value outlives function")
fn create() -> i64:
    42
val result = create()
check(result == 42)
```

</details>

#### closure captures extend lifetime

- closure captures extend lifetime


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("closure captures extend lifetime")
val x = 42
val f = \: x
check(f() == 42)
```

</details>

#### array element lifetime

- array element lifetime


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array element lifetime")
val arr = [10, 20, 30]
val first = arr[0]
check(first == 10)
```

</details>

### Drop Ordering

#### LIFO drop order

- LIFO drop order


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LIFO drop order")
val first = 1
val second = 2
val third = 3
check(first + second + third == 6)
```

</details>

#### struct fields drop with struct

- struct fields drop with struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("struct fields drop with struct")
class Pair:
    a: i64
    b: i64
val p = Pair(a: 1, b: 2)
check(p.a + p.b == 3)
```

</details>

#### array elements drop with array

- array elements drop with array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array elements drop with array")
val arr = [1, 2, 3]
check(arr.len() == 3)
```

</details>

### Temporary Lifetimes

#### temporary in expression

- temporary in expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("temporary in expression")
val result = [1, 2, 3].len()
check(result == 3)
```

</details>

#### temporary in function call

- temporary in function call


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("temporary in function call")
fn sum_len(arr: [i64]) -> i64:
    arr.len()
check(sum_len([1, 2, 3]) == 3)
```

</details>

#### chained temporaries

- chained temporaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("chained temporaries")
val result = "hello world".len()
check(result == 11)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/borrow/lifetime_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Variable Lifetimes, Reference Lifetimes, Drop Ordering, Temporary Lifetimes.
- Variable Lifetimes
- Reference Lifetimes
- Drop Ordering
- Temporary Lifetimes

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0c977258af8f7e45c83e6764988f140a9d22e2fac29a78ef6136d016fc5e262d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0c977258af8f7e45c83e6764988f140a9d22e2fac29a78ef6136d016fc5e262d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0c977258af8f7e45c83e6764988f140a9d22e2fac29a78ef6136d016fc5e262d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/borrow/lifetime_spec.spl
mirror: doc/06_spec/unit/compiler/borrow/lifetime_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/borrow/lifetime_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/borrow/lifetime_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/borrow/lifetime_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lifetime starts at declaration' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/borrow/lifetime_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lifetime ends at scope exit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/borrow/lifetime_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'nested lifetimes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
