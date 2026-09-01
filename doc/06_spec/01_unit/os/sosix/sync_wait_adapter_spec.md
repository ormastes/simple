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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

REQ-SQ-015: notification-oriented synchronous compatibility wait protocol.

## Scenarios

### SOSIX synchronous notification wait adapter

#### closes the lost-wake window by rechecking before native sleep

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SQ-015
```

</details>

#### retries a spurious signal without spinning inside the adapter

- retries a spurious signal without spinning inside the adapter
   - Expected: decision.reason equals `spurious-wake`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("retries a spurious signal without spinning inside the adapter")
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

- preserves unrelated readiness while matching operation and API
   - Expected: waits.ready_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("preserves unrelated readiness while matching operation and API")
val target = completion(9, 0x0101, SOSIX_OPERATION_COMPLETED)
val other = completion(10, 0x0102, SOSIX_OPERATION_COMPLETED)
val waits = SosixWaitSet.create()
expect(waits.watch(target.operation)).to_be(true)
expect(waits.watch(other.operation)).to_be(true)
expect(waits.notify(other)).to_be(true)
val state = SosixSyncWaitState.begin(target.operation, 0x0101, waits)
val decision = state.before_wait(waits)
expect(decision.retry).to_be(true)
expect(waits.ready_count()).to_equal(1)
```

</details>

#### rejects a matching operation completed as the wrong API

- rejects a matching operation completed as the wrong API
   - Expected: decision.outcome equals `SOSIX_SYNC_WAIT_ERROR`
   - Expected: decision.reason equals `completion-api-mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("rejects a matching operation completed as the wrong API")
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

- maps terminal completion and native termination outcomes with cleanup
   - Expected: canceled_state.after_wait(waits, SOSIX_NATIVE_WAIT_TIMED_OUT, 0).outcome equals `SOSIX_SYNC_WAIT_CANCELED`
   - Expected: timeout.outcome equals `SOSIX_SYNC_WAIT_TIMED_OUT`
   - Expected: native_canceled.outcome equals `SOSIX_SYNC_WAIT_CANCELED`
   - Expected: failed.outcome equals `SOSIX_SYNC_WAIT_ERROR`
   - Expected: failed.wait_error_status equals `-5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("maps terminal completion and native termination outcomes with cleanup")
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
expect(failed.wait_error_status).to_equal(-5)
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
- `REQ-SQ-015`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d62ff39134ab6a56c964aae7b5ae1364278fa7ea36e8d6ccdd724b5bb2a03edd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d62ff39134ab6a56c964aae7b5ae1364278fa7ea36e8d6ccdd724b5bb2a03edd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d62ff39134ab6a56c964aae7b5ae1364278fa7ea36e8d6ccdd724b5bb2a03edd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/01_unit/os/sosix/sync_wait_adapter_spec.spl
mirror: doc/06_spec/01_unit/os/sosix/sync_wait_adapter_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/sosix/sync_wait_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/sosix/sync_wait_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/sosix/sync_wait_adapter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/sosix/sync_wait_adapter_spec.spl:25:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'closes the lost-wake window by rechecking before native sleep' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/sosix/sync_wait_adapter_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retries a spurious signal without spinning inside the adapter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/sync_wait_adapter_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves unrelated readiness while matching operation and API' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/sosix/sync_wait_adapter_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a matching operation completed as the wrong API' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
