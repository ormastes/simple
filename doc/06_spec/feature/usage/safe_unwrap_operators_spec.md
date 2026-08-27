# Safe Unwrap Operators Specification

> opt unwrap or: default_value              # Use default if None

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Safe Unwrap Operators Specification

opt unwrap or: default_value              # Use default if None

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OPERATORS-SAFE-UNWRAP |
| Category | Syntax |
| Status | Implemented |
| Source | `test/feature/usage/safe_unwrap_operators_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
opt unwrap or: default_value              # Use default if None
opt unwrap else: \: lazy_default_expr     # Lazy evaluation of default
result unwrap or_return: default_on_err   # Early return with default
```

## Key Behaviors

- `unwrap or:` evaluates the default value immediately (eager)
- `unwrap else:` takes a closure for lazy evaluation (only called if needed)
- `unwrap or_return:` returns from the function with a default value on error
- Works with both Option<T> and Result<T, E> types
- Provides inline alternatives to verbose pattern matching
- Type-safe: never causes runtime panics

## Scenarios

### Safe Unwrap Operators

#### unwrap or: with eager evaluation

#### returns value when Option is Some

- returns value when Option is Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns value when Option is Some")
val opt: Option<i64> = Some(42)
val result = opt unwrap or: 0
expect result == 42
```

</details>

#### returns default when Option is None

- returns default when Option is None


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns default when Option is None")
val opt: Option<i64> = None
val result = opt unwrap or: 0
expect result == 0
```

</details>

#### works with Result Ok

- works with Result Ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with Result Ok")
val res: Result<i64, text> = Ok(42)
val result = res unwrap or: 0
expect result == 42
```

</details>

#### returns default for Result Err

- returns default for Result Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns default for Result Err")
val res: Result<i64, text> = Err("error")
val result = res unwrap or: -1
expect result == -1
```

</details>

#### evaluates default expression

- evaluates default expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates default expression")
val opt: Option<i64> = None
val result = opt unwrap or: 10 + 5
expect result == 15
```

</details>

#### handles complex default expressions

- handles complex default expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles complex default expressions")
val opt: Option<text> = None
val result = opt unwrap or: "default".upper()
expect result == "DEFAULT"
```

</details>

#### works with string defaults

- works with string defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with string defaults")
val opt: Option<text> = None
val result = opt unwrap or: "fallback"
expect result == "fallback"
```

</details>

#### preserves value type through unwrap

- preserves value type through unwrap


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("preserves value type through unwrap")
val opt: Option<i64> = Some(100)
val result = opt unwrap or: 0
# Type is still i64
expect result == 100
```

</details>

#### unwrap else: with lazy evaluation

#### returns value when Option is Some without calling closure

- returns value when Option is Some without calling closure


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns value when Option is Some without calling closure")
val opt: Option<i64> = Some(42)
var called = false
val result = opt unwrap else: \:
    called = true
    99
expect result == 42
expect called == false
```

</details>

#### calls closure only when Option is None

- calls closure only when Option is None


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls closure only when Option is None")
val opt: Option<i64> = None
var called = false
val result = opt unwrap else: \:
    called = true
    99
expect result == 99
expect called == true
```

</details>

#### works with Result Ok without evaluating closure

- works with Result Ok without evaluating closure


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with Result Ok without evaluating closure")
val res: Result<i64, text> = Ok(42)
var called = false
val result = res unwrap else: \:
    called = true
    -1
expect result == 42
expect called == false
```

</details>

#### evaluates closure for Result Err

- evaluates closure for Result Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("evaluates closure for Result Err")
val res: Result<i64, text> = Err("failed")
var called = false
val result = res unwrap else: \:
    called = true
    -1
expect result == -1
expect called == true
```

</details>

#### closure can perform side effects

- closure can perform side effects


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("closure can perform side effects")
var side_effect = 0
val opt: Option<i64> = None
val result = opt unwrap else: \:
    side_effect = 100
    42
expect result == 42
expect side_effect == 100
```

</details>

#### lazy evaluation skips expensive computation when value exists

- lazy evaluation skips expensive computation when value exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("lazy evaluation skips expensive computation when value exists")
val opt: Option<i64> = Some(1)
var expensive_called = false
val result = opt unwrap else: \:
    expensive_called = true
    999
expect result == 1
expect expensive_called == false
```

</details>

#### unwrap or_return: with early return

#### returns value when present

- returns value when present


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns value when present")
fn get_value_or_early() -> i64:
    val opt: Option<i64> = Some(42)
    val value = opt unwrap or_return: 0
    value + 1
expect get_value_or_early() == 43
```

</details>

#### returns default when None

- returns default when None


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns default when None")
fn get_value_or_early() -> i64:
    val opt: Option<i64> = None
    val value = opt unwrap or_return: 0
    value + 1  # This code never executes
expect get_value_or_early() == 0
```

</details>

#### works with Result

- works with Result


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works with Result")
fn parse_number_or_early() -> i64:
    val res: Result<i64, text> = Ok(42)
    val value = res unwrap or_return: -1
    value * 2
expect parse_number_or_early() == 84
```

</details>

#### returns default for Result Err

- returns default for Result Err


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns default for Result Err")
fn parse_number_or_early() -> i64:
    val res: Result<i64, text> = Err("parse error")
    val value = res unwrap or_return: -1
    value * 2
expect parse_number_or_early() == -1
```

</details>

#### chaining and composition

#### can chain multiple unwrap operations

- can chain multiple unwrap operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("can chain multiple unwrap operations")
fn chain_result(opt1, opt2):
    val v1 = opt1 unwrap or: 0
    val v2 = opt2 unwrap or: 0
    v1 + v2
expect chain_result(Some(10), Some(20)) == 30
expect chain_result(Some(10), None) == 10
expect chain_result(None, Some(20)) == 20
expect chain_result(None, None) == 0
```

</details>

#### works in nested expressions

- works in nested expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("works in nested expressions")
val opt: Option<i64> = Some(5)
val result = (opt unwrap or: 0) * 2 + 10
expect result == 20
```

</details>

#### type safety

#### preserves Option type semantics

- preserves Option type semantics


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("preserves Option type semantics")
val maybe_value: Option<text> = Some("hello")
val text_result = maybe_value unwrap or: "world"
expect text_result == "hello"
```

</details>

#### handles nested Option types

- handles nested Option types


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles nested Option types")
val nested: Option<Option<i64>> = Some(Some(42))
# Unwraps outer layer
val inner = nested unwrap or: Some(0)
expect inner == Some(42)
```

</details>

#### preserves Result error information

- preserves Result error information


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("preserves Result error information")
val result: Result<i64, text> = Err("error message")
val recovered = result unwrap or: 0
expect recovered == 0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
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

- Canonical SPipe generation for source `3db7789976f6135482e8a69f340c6177b34fbbc2a0d7d542c72115bfa204d288`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3db7789976f6135482e8a69f340c6177b34fbbc2a0d7d542c72115bfa204d288`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3db7789976f6135482e8a69f340c6177b34fbbc2a0d7d542c72115bfa204d288`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/feature/usage/safe_unwrap_operators_spec.spl
mirror: doc/06_spec/feature/usage/safe_unwrap_operators_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/safe_unwrap_operators_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/safe_unwrap_operators_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/safe_unwrap_operators_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns value when Option is Some' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/safe_unwrap_operators_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns default when Option is None' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/safe_unwrap_operators_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'works with Result Ok' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/safe_unwrap_operators_spec.spl:207:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can chain multiple unwrap operations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
