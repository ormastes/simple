# promise_spec

> Promise<T> Specification Tests

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# promise_spec

Promise<T> Specification Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/concurrency/promise_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Promise<T> Specification Tests

Tests for the Promise type implementing async-by-default semantics.

NOTE: Simple language uses Result<T, E> for error handling, not exceptions.
Promise module has been updated to work without try-catch blocks.

## Scenarios

### Promise<T> - Basic Operations

#### creates a resolved promise

- creates a resolved promise


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates a resolved promise")
val p = make_resolved(42)
expect p.is_resolved()
expect not p.is_pending()
```

</details>

#### creates a rejected promise

- creates a rejected promise


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates a rejected promise")
val p = make_rejected("error")
expect p.is_rejected()
expect not p.is_pending()
```

</details>

#### creates a promise with executor that resolves

- creates a promise with executor that resolves


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates a promise with executor that resolves")
val p = Promise.new(\resolve, reject: resolve(100))
expect p.is_resolved()
```

</details>

#### creates a promise with executor that rejects

- creates a promise with executor that rejects


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates a promise with executor that rejects")
val p = Promise.new(\resolve, reject: reject("failed"))
expect p.is_rejected()
```

</details>

#### starts as pending before executor runs

- starts as pending before executor runs


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("starts as pending before executor runs")
# For immediate executors, promise resolves synchronously
# This tests the initial state construction
val p = Promise {
    state: PromiseState.Pending,
    callbacks: []
}
expect p.is_pending()
```

</details>

### Promise<T> - State Management

#### resolves only once

- resolves only once


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("resolves only once")
var resolve_count = 0
val p = Promise.new(\resolve, reject:
    resolve(1)
    resolve(2)  # Should be ignored
)
expect p.is_resolved()
# Verify first value was used (can't check exact value without await)
```

</details>

#### rejects only once

- rejects only once


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects only once")
var reject_count = 0
val p = Promise.new(\resolve, reject:
    reject("first")
    reject("second")  # Should be ignored
)
expect p.is_rejected()
```

</details>

#### cannot transition from resolved to rejected

- cannot transition from resolved to rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("cannot transition from resolved to rejected")
val p = Promise.new(\resolve, reject:
    resolve(42)
    reject("error")  # Should be ignored
)
expect p.is_resolved()
expect not p.is_rejected()
```

</details>

#### cannot transition from rejected to resolved

- cannot transition from rejected to resolved


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("cannot transition from rejected to resolved")
val p = Promise.new(\resolve, reject:
    reject("error")
    resolve(42)  # Should be ignored
)
expect p.is_rejected()
expect not p.is_resolved()
```

</details>

#### preserves state after creation

- preserves state after creation


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves state after creation")
val p1 = make_resolved(10)
val p2 = make_rejected("err")

# Check states are stable
expect p1.is_resolved()
expect p2.is_rejected()
```

</details>

### Promise<T> - Type Safety

#### can hold integer values

- can hold integer values


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("can hold integer values")
val p = make_resolved(42)
expect p.is_resolved()
```

</details>

#### can hold string values

- can hold string values


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("can hold string values")
val p = make_resolved("hello")
expect p.is_resolved()
```

</details>

#### can hold errors as strings

- can hold errors as strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("can hold errors as strings")
val p = make_rejected("error message")
expect p.is_rejected()
```

</details>

### Promise<T> - Edge Cases

#### handles nil resolution

- handles nil resolution


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles nil resolution")
val p = make_resolved(nil)
expect p.is_resolved()
```

</details>

#### handles nil rejection

- handles nil rejection


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles nil rejection")
val p = make_rejected(nil)
expect p.is_rejected()
```

</details>

#### handles empty callback list

- handles empty callback list


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles empty callback list")
val p = Promise {
    state: PromiseState.Resolved(42),
    callbacks: []
}
expect p.is_resolved()
```

</details>

### Promise<T> - Integration

#### works with match expressions on state

- works with match expressions on state


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("works with match expressions on state")
val p = make_resolved(100)
var matched = false

match p.state:
    case PromiseState.Resolved(v):
        matched = true
    case _:
        matched = false

expect matched
```

</details>

#### works with match expressions for rejection

- works with match expressions for rejection


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("works with match expressions for rejection")
val p = make_rejected("error")
var matched = false

match p.state:
    case PromiseState.Rejected(e):
        matched = true
    case _:
        matched = false

expect matched
```

</details>

#### executor receives both callbacks

- executor receives both callbacks


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("executor receives both callbacks")
var resolve_called = false
var reject_called = false

val p1 = Promise.new(\resolve, reject:
    resolve_called = true
    resolve(1)
)

val p2 = Promise.new(\resolve, reject:
    reject_called = true
    reject("err")
)

expect resolve_called
expect reject_called
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `08a2ab186a623eeec059d66b19da95fed03e26fafbf837f667bb062efe0a9970`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `08a2ab186a623eeec059d66b19da95fed03e26fafbf837f667bb062efe0a9970`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `08a2ab186a623eeec059d66b19da95fed03e26fafbf837f667bb062efe0a9970`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/std/concurrency/promise_spec.spl
mirror: doc/06_spec/01_unit/lib/std/concurrency/promise_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/std/concurrency/promise_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/std/concurrency/promise_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/std/concurrency/promise_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a resolved promise' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/concurrency/promise_spec.spl:150:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a rejected promise' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/concurrency/promise_spec.spl:157:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates a promise with executor that resolves' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/concurrency/promise_spec.spl:241:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can hold integer values' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/std/concurrency/promise_spec.spl:247:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can hold string values' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/std/concurrency/promise_spec.spl:253:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can hold errors as strings' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
