# Thread Sffi Specification

> Tests covering Thread Sffi.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Thread Sffi Specification

## Scenarios

### Thread Sffi

#### should declare thread management externs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should declare thread management externs
   - Expected: src contains `extern fn spl_thread_create`
   - Expected: src contains `extern fn spl_thread_join`
   - Expected: src contains `extern fn spl_thread_detach`
   - Expected: src contains `extern fn spl_thread_current_id() -> i64`
   - Expected: src contains `extern fn spl_thread_cpu_count() -> i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should declare thread management externs")
val src = thread_sffi_source()
expect(src.contains("extern fn spl_thread_create")).to_equal(true)
expect(src.contains("extern fn spl_thread_join")).to_equal(true)
expect(src.contains("extern fn spl_thread_detach")).to_equal(true)
expect(src.contains("extern fn spl_thread_current_id() -> i64")).to_equal(true)
expect(src.contains("extern fn spl_thread_cpu_count() -> i64")).to_equal(true)
```

</details>

#### should wrap thread handles with validity guards

- should wrap thread handles with validity guards
   - Expected: src contains `class ThreadHandle`
   - Expected: src contains `static fn invalid() -> ThreadHandle`
   - Expected: src contains `static fn from_raw(handle: i64) -> ThreadHandle`
   - Expected: src contains `fn is_valid() -> bool`
   - Expected: src contains `if not self.is_valid()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should wrap thread handles with validity guards")
val src = thread_sffi_source()
expect(src.contains("class ThreadHandle")).to_equal(true)
expect(src.contains("static fn invalid() -> ThreadHandle")).to_equal(true)
expect(src.contains("static fn from_raw(handle: i64) -> ThreadHandle")).to_equal(true)
expect(src.contains("fn is_valid() -> bool")).to_equal(true)
expect(src.contains("if not self.is_valid()")).to_equal(true)
```

</details>

#### should expose mutex primitives through handle methods

- should expose mutex primitives through handle methods
   - Expected: src contains `extern fn spl_mutex_create() -> i64`
   - Expected: src contains `class MutexHandle`
   - Expected: src contains `fn lock() -> bool`
   - Expected: src contains `fn try_lock() -> bool`
   - Expected: src contains `fn unlock() -> bool`
   - Expected: src contains `fn mutex_create() -> MutexHandle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should expose mutex primitives through handle methods")
val src = thread_sffi_source()
expect(src.contains("extern fn spl_mutex_create() -> i64")).to_equal(true)
expect(src.contains("class MutexHandle")).to_equal(true)
expect(src.contains("fn lock() -> bool")).to_equal(true)
expect(src.contains("fn try_lock() -> bool")).to_equal(true)
expect(src.contains("fn unlock() -> bool")).to_equal(true)
expect(src.contains("fn mutex_create() -> MutexHandle")).to_equal(true)
```

</details>

#### should expose condition variable wait and wake primitives

- should expose condition variable wait and wake primitives
   - Expected: src contains `class CondVarHandle`
   - Expected: src contains `fn wait(mutex: MutexHandle) -> bool`
   - Expected: src contains `fn wait_timeout(mutex: MutexHandle, timeout_ms: i64) -> bool`
   - Expected: src contains `fn signal() -> bool`
   - Expected: src contains `fn broadcast() -> bool`
   - Expected: src contains `fn condvar_create() -> CondVarHandle`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should expose condition variable wait and wake primitives")
val src = thread_sffi_source()
expect(src.contains("class CondVarHandle")).to_equal(true)
expect(src.contains("fn wait(mutex: MutexHandle) -> bool")).to_equal(true)
expect(src.contains("fn wait_timeout(mutex: MutexHandle, timeout_ms: i64) -> bool")).to_equal(true)
expect(src.contains("fn signal() -> bool")).to_equal(true)
expect(src.contains("fn broadcast() -> bool")).to_equal(true)
expect(src.contains("fn condvar_create() -> CondVarHandle")).to_equal(true)
```

</details>

#### should retain interpreter backed tls semaphore and event helpers

- should retain interpreter backed tls semaphore and event helpers
   - Expected: src contains `fn tls_key_alloc`
   - Expected: src contains `fn tls_key_set`
   - Expected: src contains `fn tls_key_get`
   - Expected: src contains `fn semaphore_create`
   - Expected: src contains `fn event_wait_create`
   - Expected: src contains `fn event_wait_wait`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should retain interpreter backed tls semaphore and event helpers")
val src = thread_sffi_source()
expect(src.contains("fn tls_key_alloc")).to_equal(true)
expect(src.contains("fn tls_key_set")).to_equal(true)
expect(src.contains("fn tls_key_get")).to_equal(true)
expect(src.contains("fn semaphore_create")).to_equal(true)
expect(src.contains("fn event_wait_create")).to_equal(true)
expect(src.contains("fn event_wait_wait")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/thread_sffi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Thread Sffi.
- Thread Sffi

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `4aa3cfdd02527919a0168d1780f954fcd9c7d417a7642272b0be16bb524a9fcd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4aa3cfdd02527919a0168d1780f954fcd9c7d417a7642272b0be16bb524a9fcd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4aa3cfdd02527919a0168d1780f954fcd9c7d417a7642272b0be16bb524a9fcd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/nogc_async_mut/thread_sffi_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/thread_sffi_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/thread_sffi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/thread_sffi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/thread_sffi_spec.spl:18:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should declare thread management externs' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_async_mut/thread_sffi_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should declare thread management externs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/thread_sffi_spec.spl:28:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should wrap thread handles with validity guards' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_async_mut/thread_sffi_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should wrap thread handles with validity guards' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/thread_sffi_spec.spl:38:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose mutex primitives through handle methods' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_async_mut/thread_sffi_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose mutex primitives through handle methods' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/thread_sffi_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose condition variable wait and wake primitives' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/nogc_async_mut/thread_sffi_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain interpreter backed tls semaphore and event helpers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
