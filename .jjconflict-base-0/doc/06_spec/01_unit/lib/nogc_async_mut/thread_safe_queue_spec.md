# Thread Safe Queue Specification

> Tests covering Thread Safe Queue.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Thread Safe Queue Specification

## Scenarios

### Thread Safe Queue

#### should expose mutex protected queue operations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose mutex protected queue operations
   - Expected: src contains `class ThreadSafeQueue`
   - Expected: src contains `items: [usize]`
   - Expected: src contains `head: usize`
   - Expected: src contains `mutex: MutexHandle`
   - Expected: src contains `not_empty: CondVarHandle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should expose mutex protected queue operations")
val src = queue_source()
expect(src.contains("class ThreadSafeQueue")).to_equal(true)
expect(src.contains("items: [usize]")).to_equal(true)
expect(src.contains("head: usize")).to_equal(true)
expect(src.contains("mutex: MutexHandle")).to_equal(true)
expect(src.contains("not_empty: CondVarHandle")).to_equal(true)
```

</details>

#### should create mutex and condition variable resources

- should create mutex and condition variable resources
   - Expected: src contains `mutex: mutex_create()`
   - Expected: src contains `not_empty: condvar_create()`
   - Expected: src contains `static fn new() -> ThreadSafeQueue`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should create mutex and condition variable resources")
val src = queue_source()
expect(src.contains("mutex: mutex_create()")).to_equal(true)
expect(src.contains("not_empty: condvar_create()")).to_equal(true)
expect(src.contains("static fn new() -> ThreadSafeQueue")).to_equal(true)
```

</details>

#### should guard push and signal waiters

- should guard push and signal waiters
   - Expected: src contains `me push(item: usize)`
   - Expected: src contains `self.mutex.lock()`
   - Expected: src contains `self.items = self.items.push(item)`
   - Expected: src contains `self.not_empty.signal()`
   - Expected: src contains `self.mutex.unlock()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should guard push and signal waiters")
val src = queue_source()
expect(src.contains("me push(item: usize)")).to_equal(true)
expect(src.contains("self.mutex.lock()")).to_equal(true)
expect(src.contains("self.items = self.items.push(item)")).to_equal(true)
expect(src.contains("self.not_empty.signal()")).to_equal(true)
expect(src.contains("self.mutex.unlock()")).to_equal(true)
```

</details>

#### should return zero sentinel for empty or timed out pops

- should return zero sentinel for empty or timed out pops
   - Expected: src contains `me try_pop() -> usize`
   - Expected: src contains `me pop_blocking(timeout_ms: i64) -> usize`
   - Expected: src contains `return 0`
   - Expected: src contains `var result = 0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should return zero sentinel for empty or timed out pops")
val src = queue_source()
expect(src.contains("me try_pop() -> usize")).to_equal(true)
expect(src.contains("me pop_blocking(timeout_ms: i64) -> usize")).to_equal(true)
expect(src.contains("return 0")).to_equal(true)
expect(src.contains("var result = 0")).to_equal(true)
```

</details>

#### uses a consumed-prefix cursor instead of slicing every pop

- uses a consumed-prefix cursor instead of slicing every pop
   - Expected: src contains `me pop_unlocked() -> usize`
   - Expected: src contains `self.items[self.head]`
   - Expected: src does not contain `self.items = self.items[1:]`
   - Expected: src contains `self.items = self.items[self.head:]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses a consumed-prefix cursor instead of slicing every pop")
val src = queue_source()
expect(src.contains("me pop_unlocked() -> usize")).to_equal(true)
expect(src.contains("self.items[self.head]")).to_equal(true)
expect(src.contains("self.items = self.items[1:]")).to_equal(false)
expect(src.contains("self.items = self.items[self.head:]")).to_equal(true)
```

</details>

#### should expose size clear and destroy lifecycle methods

- should expose size clear and destroy lifecycle methods
   - Expected: src contains `fn len() -> usize`
   - Expected: src contains `fn is_empty() -> bool`
   - Expected: src contains `me clear()`
   - Expected: src contains `me destroy()`
   - Expected: src contains `self.not_empty.destroy()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should expose size clear and destroy lifecycle methods")
val src = queue_source()
expect(src.contains("fn len() -> usize")).to_equal(true)
expect(src.contains("fn is_empty() -> bool")).to_equal(true)
expect(src.contains("me clear()")).to_equal(true)
expect(src.contains("me destroy()")).to_equal(true)
expect(src.contains("self.not_empty.destroy()")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/thread_safe_queue_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Thread Safe Queue.
- Thread Safe Queue

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `a01bcc2b7744dba2880cc4597abc245f12ab1b57f6406ecfb22564137ae64fb5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a01bcc2b7744dba2880cc4597abc245f12ab1b57f6406ecfb22564137ae64fb5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a01bcc2b7744dba2880cc4597abc245f12ab1b57f6406ecfb22564137ae64fb5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/nogc_async_mut/thread_safe_queue_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/thread_safe_queue_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/thread_safe_queue_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/thread_safe_queue_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/thread_safe_queue_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose mutex protected queue operations' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_async_mut/thread_safe_queue_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose mutex protected queue operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/thread_safe_queue_spec.spl:28:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should create mutex and condition variable resources' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_async_mut/thread_safe_queue_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should create mutex and condition variable resources' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/thread_safe_queue_spec.spl:36:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should guard push and signal waiters' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_async_mut/thread_safe_queue_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should guard push and signal waiters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/thread_safe_queue_spec.spl:46:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should return zero sentinel for empty or timed out pops' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_async_mut/thread_safe_queue_spec.spl:64:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose size clear and destroy lifecycle methods' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
