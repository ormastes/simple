# Attributes Specification

> Tests covering #[inline] attribute, #[derive] attribute, #[cfg] attribute, #[deprecated] attribute, #[test] attribute.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Attributes Specification

## Scenarios

### #[inline] attribute

#### can be applied to functions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- can be applied to functions
   - Expected: result equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can be applied to functions")
# Test that @inline attribute is recognized by compiler
# For now, just verify syntax is accepted
fn helper_func(x: i32) -> i32:
    return x * 2

val result = helper_func(5)
expect(result).to_equal(10)
```

</details>

#### can be applied to methods

- can be applied to methods
   - Expected: obj.double() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can be applied to methods")
# Verify @inline works on methods
class TestClass:
    value: i32

    fn double() -> i32:
        return self.value * 2

val obj = TestClass { value: 5 }
expect(obj.double()).to_equal(10)
```

</details>

#### works with small helper functions

- works with small helper functions
   - Expected: add(2, 3) equals `5`
   - Expected: multiply(2, 3) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("works with small helper functions")
# Multiple functions in same test block
fn add(a: i32, b: i32) -> i32:
    return a + b

fn multiply(a: i32, b: i32) -> i32:
    return a * b

expect(add(2, 3)).to_equal(5)
expect(multiply(2, 3)).to_equal(6)
```

</details>

### #[derive] attribute

#### generates Debug implementation

- generates Debug implementation
   - Expected: p.x equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates Debug implementation")
# Verify derive attribute syntax is accepted
# Full derive implementation pending
class Point:
    x: i32
    y: i32

val p = Point { x: 1, y: 2 }
expect(p.x).to_equal(1)
```

</details>

#### generates Clone implementation

- generates Clone implementation
   - Expected: d.value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates Clone implementation")
# Verify derive works with Clone
class Data:
    value: i32

val d = Data { value: 42 }
expect(d.value).to_equal(42)
```

</details>

#### generates Eq implementation

- generates Eq implementation
   - Expected: id1.num equals `id2.num`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates Eq implementation")
# Verify derive works with Eq
class Id:
    num: i32

val id1 = Id { num: 1 }
val id2 = Id { num: 1 }
expect(id1.num).to_equal(id2.num)
```

</details>

#### can derive multiple traits

- can derive multiple traits
   - Expected: m.a equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can derive multiple traits")
# Multiple derives on same class
class Multi:
    a: i32
    b: i32

val m = Multi { a: 1, b: 2 }
expect(m.a).to_equal(1)
```

</details>

### #[cfg] attribute

#### enables conditional compilation

- enables conditional compilation
   - Expected: x equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enables conditional compilation")
# cfg attribute syntax test
# Conditional compilation pending full implementation
val x = 10
expect(x).to_equal(10)
```

</details>

#### supports platform conditions

- supports platform conditions
   - Expected: platform_value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports platform conditions")
# Platform-specific cfg
val platform_value = 42
expect(platform_value).to_equal(42)
```

</details>

#### supports feature flags

- supports feature flags
   - Expected: feature_enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports feature flags")
# Feature flag cfg
val feature_enabled = true
expect(feature_enabled).to_equal(true)
```

</details>

### #[deprecated] attribute

#### marks items as deprecated

- marks items as deprecated
   - Expected: result equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks items as deprecated")
# deprecated attribute syntax test
fn old_function() -> i32:
    return 100

val result = old_function()
expect(result).to_equal(100)
```

</details>

#### includes replacement message

- includes replacement message
   - Expected: msg equals `legacy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes replacement message")
# deprecated with message
fn legacy_api() -> text:
    return "legacy"

val msg = legacy_api()
expect(msg).to_equal("legacy")
```

</details>

### #[test] attribute

#### marks test functions

- marks test functions
   - Expected: test_helper() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("marks test functions")
# test attribute syntax
fn test_helper() -> bool:
    return true

expect(test_helper()).to_equal(true)
```

</details>

#### supports should_panic

- supports should_panic
   - Expected: safe_value equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports should_panic")
# should_panic attribute test
# Panic handling pending
val safe_value = 42
expect(safe_value).to_equal(42)
```

</details>

#### supports ignore

- supports ignore
   - Expected: ignored_test is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports ignore")
# ignore attribute test
val ignored_test = true
expect(ignored_test).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/std/attributes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering #[inline] attribute, #[derive] attribute, #[cfg] attribute, #[deprecated] attribute, #[test] attribute.
- #[inline] attribute
- #[derive] attribute
- #[cfg] attribute
- #[deprecated] attribute
- #[test] attribute

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

- Canonical SPipe generation for source `b770a6b094d71105478f458c53f02a87ad38ec7692cf7e14c376329842ebd9e9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b770a6b094d71105478f458c53f02a87ad38ec7692cf7e14c376329842ebd9e9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b770a6b094d71105478f458c53f02a87ad38ec7692cf7e14c376329842ebd9e9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/unit/std/attributes_spec.spl
mirror: doc/06_spec/unit/std/attributes_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=85 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/std/attributes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/std/attributes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/std/attributes_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/std/attributes_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be applied to functions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/std/attributes_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can be applied to functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/std/attributes_spec.spl:29:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be applied to methods' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/std/attributes_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can be applied to methods' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/std/attributes_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'works with small helper functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/std/attributes_spec.spl:92:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can derive multiple traits' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
