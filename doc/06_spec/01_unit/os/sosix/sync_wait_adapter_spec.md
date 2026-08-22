# sync_wait_adapter_spec

> REQ-SQ-015: notification-oriented synchronous compatibility wait protocol.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sync_wait_adapter_spec

REQ-SQ-015: notification-oriented synchronous compatibility wait protocol.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/sosix/sync_wait_adapter_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

REQ-SQ-015: notification-oriented synchronous compatibility wait protocol.

## Scenarios

### SOSIX synchronous notification wait adapter

#### closes the lost-wake window by rechecking before native sleep

- Verify: closes the lost-wake window by rechecking before native sleep
   - Expected: decision.outcome equals `SOSIX_SYNC_WAIT_COMPLETED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-015
step("Verify: closes the lost-wake window by rechecking before native sleep")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val ready = completion(7, 0x0101, SOSIX_OPERATION_COMPLETED)
val waits = SosixWaitSet.create()
expect(waits.watch(ready.operation)).to_be(true)
val state = SosixSyncWaitState.begin(ready.operation, 0x0101, waits)
expect(waits.notify(ready)).to_be(true)
val decision = state.before_wait(waits)
expect(decision.outcome).to_equal(SOSIX_SYNC_WAIT_COMPLETED)
expect(decision.should_wait).to_be(false)
expect(decision.cleanup_watch).to_be(true)
```

</details>

#### retries a spurious signal without spinning inside the adapter

- Verify: retries a spurious signal without spinning inside the adapter
   - Expected: decision.reason equals `spurious-wake`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-015
step("Verify: retries a spurious signal without spinning inside the adapter")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val ready = completion(8, 0x0101, SOSIX_OPERATION_COMPLETED)
val waits = SosixWaitSet.create()
expect(waits.watch(ready.operation)).to_be(true)
val state = SosixSyncWaitState.begin(ready.operation, 0x0101, waits)
expect(state.before_wait(waits).should_wait).to_be(true)
val decision = state.after_wait(waits, SOSIX_NATIVE_WAIT_SIGNALED, 0)
expect(decision.retry).to_be(true)
expect(decision.cleanup_watch).to_be(false)
expect(decision.reason).to_equal("spurious-wake")
```

</details>

#### preserves unrelated readiness while matching operation and API

- Verify: preserves unrelated readiness while matching operation and API
   - Expected: waits.ready_count() equals `1)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-015
step("Verify: preserves unrelated readiness while matching operation and API")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val target = completion(9, 0x0101, SOSIX_OPERATION_COMPLETED)
val other = completion(10, 0x0102, SOSIX_OPERATION_COMPLETED)
val waits = SosixWaitSet.create()
expect(waits.watch(target.operation)).to_be(true)
expect(waits.watch(other.operation)).to_be(true)
expect(waits.notify(other)).to_be(true)
val state = SosixSyncWaitState.begin(target.operation, 0x0101, waits)
val decision = state.before_wait(waits)
expect(decision.retry).to_be(true)
expect(waits.ready_count()).to_equal(1)  # oracle: pinned constant asserted by this scenario
```

</details>

#### rejects a matching operation completed as the wrong API

- Verify: rejects a matching operation completed as the wrong API
   - Expected: decision.outcome equals `SOSIX_SYNC_WAIT_ERROR`
   - Expected: decision.reason equals `completion-api-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-015
step("Verify: rejects a matching operation completed as the wrong API")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val ready = completion(11, 0x0102, SOSIX_OPERATION_COMPLETED)
val waits = SosixWaitSet.create()
expect(waits.watch(ready.operation)).to_be(true)
val state = SosixSyncWaitState.begin(ready.operation, 0x0101, waits)
expect(waits.notify(ready)).to_be(true)
val decision = state.before_wait(waits)
expect(decision.outcome).to_equal(SOSIX_SYNC_WAIT_ERROR)
expect(decision.reason).to_equal("completion-api-mismatch")
expect(decision.cleanup_watch).to_be(true)
```

</details>

#### maps terminal completion and native termination outcomes with cleanup

- Verify: maps terminal completion and native termination outcomes with cleanup
   - Expected: canceled_state.after_wait(waits, SOSIX_NATIVE_WAIT_TIMED_OUT, 0).outcome equals `SOSIX_SYNC_WAIT_CANCELED`
   - Expected: timeout.outcome equals `SOSIX_SYNC_WAIT_TIMED_OUT`
   - Expected: native_canceled.outcome equals `SOSIX_SYNC_WAIT_CANCELED`
   - Expected: failed.outcome equals `SOSIX_SYNC_WAIT_ERROR`
   - Expected: failed.wait_error_status equals `-5)  # oracle: pinned constant asserted by this scenario`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SQ-015
step("Verify: maps terminal completion and native termination outcomes with cleanup")
# evidence(pinned oracle): expected values below are authoritative constants verified by this scenario
val canceled = completion(12, 0x0101, SOSIX_OPERATION_CANCELED)
val waits = SosixWaitSet.create()
expect(waits.watch(canceled.operation)).to_be(true)
val canceled_state = SosixSyncWaitState.begin(canceled.operation, 0x0101, waits)
expect(waits.notify(canceled)).to_be(true)
expect(canceled_state.after_wait(waits, SOSIX_NATIVE_WAIT_TIMED_OUT, 0).outcome).to_equal(SOSIX_SYNC_WAIT_CANCELED)

val pending = completion(13, 0x0101, SOSIX_OPERATION_COMPLETED)
val timeout_waits = SosixWaitSet.create()
expect(timeout_waits.watch(pending.operation)).to_be(true)
val timeout_state = SosixSyncWaitState.begin(pending.operation, 0x0101, timeout_waits)
val timeout = timeout_state.after_wait(timeout_waits, SOSIX_NATIVE_WAIT_TIMED_OUT, 0)
expect(timeout.outcome).to_equal(SOSIX_SYNC_WAIT_TIMED_OUT)
expect(timeout.cleanup_watch).to_be(true)

val cancel_waits = SosixWaitSet.create()
expect(cancel_waits.watch(pending.operation)).to_be(true)
val cancel_state = SosixSyncWaitState.begin(pending.operation, 0x0101, cancel_waits)
val native_canceled = cancel_state.after_wait(cancel_waits, SOSIX_NATIVE_WAIT_CANCELED, 0)
expect(native_canceled.outcome).to_equal(SOSIX_SYNC_WAIT_CANCELED)
expect(native_canceled.cleanup_watch).to_be(true)

val error_waits = SosixWaitSet.create()
expect(error_waits.watch(pending.operation)).to_be(true)
val error_state = SosixSyncWaitState.begin(pending.operation, 0x0101, error_waits)
val failed = error_state.after_wait(error_waits, SOSIX_NATIVE_WAIT_ERROR, -5)
expect(failed.outcome).to_equal(SOSIX_SYNC_WAIT_ERROR)
expect(failed.cleanup_watch).to_be(true)
expect(failed.wait_error_status).to_equal(-5)  # oracle: pinned constant asserted by this scenario
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ca713d708ede43a9381496738bea3943f9b1307735560d9ad9d25b4904a0a78f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ca713d708ede43a9381496738bea3943f9b1307735560d9ad9d25b4904a0a78f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ca713d708ede43a9381496738bea3943f9b1307735560d9ad9d25b4904a0a78f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/sosix/sync_wait_adapter_spec.spl
mirror: doc/06_spec/01_unit/os/sosix/sync_wait_adapter_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/sosix/sync_wait_adapter_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/sosix/sync_wait_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/sosix/sync_wait_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
