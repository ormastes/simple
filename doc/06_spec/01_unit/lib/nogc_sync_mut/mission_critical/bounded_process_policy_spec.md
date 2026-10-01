# Bounded Process Policy Specification

> Tests covering bounded mission-critical process policy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bounded Process Policy Specification

## Scenarios

### bounded mission-critical process policy

#### POLICY-MCI-PROC rejects non-positive signal and wait targets

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- POLICY-MCI-PROC rejects non-positive signal and wait targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("POLICY-MCI-PROC rejects non-positive signal and wait targets")
expect(validate_process_signal_pid(-1).accepted).to_be(false)
expect(validate_process_signal_pid(0).accepted).to_be(false)
expect(validate_process_signal_pid(1).accepted).to_be(true)
```

</details>

#### POLICY-MCI-PROC admits exact worker and queue boundaries

- POLICY-MCI-PROC admits exact worker and queue boundaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("POLICY-MCI-PROC admits exact worker and queue boundaries")
val worker = BoundedWorkPoolV1(
    max_workers: 2,
    max_pending: 1,
    active_workers: 1,
    pending_work: 0
)
val queued = BoundedWorkPoolV1(
    max_workers: 2,
    max_pending: 1,
    active_workers: 2,
    pending_work: 0
)
expect(admit_bounded_work(worker).accepted).to_be(true)
expect(admit_bounded_work(queued).accepted).to_be(true)
```

</details>

#### POLICY-MCI-PROC rejects work beyond the fixed queue

- POLICY-MCI-PROC rejects work beyond the fixed queue
   - Expected: receipt.observed equals `1`
   - Expected: receipt.limit equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("POLICY-MCI-PROC rejects work beyond the fixed queue")
val full = BoundedWorkPoolV1(
    max_workers: 2,
    max_pending: 1,
    active_workers: 2,
    pending_work: 1
)
val receipt = admit_bounded_work(full)
expect(receipt.accepted).to_be(false)
expect(receipt.observed).to_equal(1)
expect(receipt.limit).to_equal(1)
```

</details>

#### POLICY-MCI-PROC admits exact capture limits and rejects one byte beyond

- POLICY-MCI-PROC admits exact capture limits and rejects one byte beyond


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("POLICY-MCI-PROC admits exact capture limits and rejects one byte beyond")
val exact = BoundedProcessCaptureV1(
    max_stdout_bytes: 16,
    max_stderr_bytes: 8,
    stdout_bytes: 16,
    stderr_bytes: 8
)
val overflow = BoundedProcessCaptureV1(
    max_stdout_bytes: 16,
    max_stderr_bytes: 8,
    stdout_bytes: 17,
    stderr_bytes: 8
)
val stderr_overflow = BoundedProcessCaptureV1(
    max_stdout_bytes: 16,
    max_stderr_bytes: 8,
    stdout_bytes: 16,
    stderr_bytes: 9
)
expect(admit_bounded_capture(exact).accepted).to_be(true)
expect(admit_bounded_capture(overflow).accepted).to_be(false)
expect(admit_bounded_capture(stderr_overflow).accepted).to_be(false)
```

</details>

#### POLICY-MCI-PROC rejects invalid capacities before admission

- POLICY-MCI-PROC rejects invalid capacities before admission
   - Expected: receipt.observed equals `3`
   - Expected: receipt.limit equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("POLICY-MCI-PROC rejects invalid capacities before admission")
val invalid = BoundedWorkPoolV1(
    max_workers: 0,
    max_pending: 1,
    active_workers: 0,
    pending_work: 0
)
expect(admit_bounded_work(invalid).accepted).to_be(false)

val overcommitted = BoundedWorkPoolV1(
    max_workers: 2,
    max_pending: 4,
    active_workers: 3,
    pending_work: 0
)
val receipt = admit_bounded_work(overcommitted)
expect(receipt.accepted).to_be(false)
expect(receipt.observed).to_equal(3)
expect(receipt.limit).to_equal(2)
```

</details>

#### POLICY-MCI-PROC keeps worker and process in-flight ceilings distinct

- POLICY-MCI-PROC keeps worker and process in-flight ceilings distinct
   - Expected: receipt.code equals `ProcessSafetyCodeV1.InFlightLimitReached`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("POLICY-MCI-PROC keeps worker and process in-flight ceilings distinct")
val policy = BoundedProcessPolicyV2(max_timeout_ms: 1000, max_in_flight: 2)
val exact_last_slot = BoundedProcessAdmissionV2(
    policy: policy, requested_timeout_ms: 1000,
    active_workers: 7, in_flight_processes: 1)
val full = BoundedProcessAdmissionV2(
    policy: policy, requested_timeout_ms: 1000,
    active_workers: 0, in_flight_processes: 2)
expect(admit_bounded_process(exact_last_slot).accepted).to_be(true)
val receipt = admit_bounded_process(full)
expect(receipt.accepted).to_be(false)
expect(receipt.code).to_equal(ProcessSafetyCodeV1.InFlightLimitReached)
```

</details>

#### POLICY-MCI-PROC admits the exact timeout and rejects zero and one beyond

- POLICY-MCI-PROC admits the exact timeout and rejects zero and one beyond
   - Expected: beyond.code equals `ProcessSafetyCodeV1.TimeoutLimitReached`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("POLICY-MCI-PROC admits the exact timeout and rejects zero and one beyond")
val policy = BoundedProcessPolicyV2(max_timeout_ms: 1000, max_in_flight: 1)
expect(admit_bounded_process(BoundedProcessAdmissionV2(
    policy: policy, requested_timeout_ms: 1000,
    active_workers: 0, in_flight_processes: 0)).accepted).to_be(true)
expect(admit_bounded_process(BoundedProcessAdmissionV2(
    policy: policy, requested_timeout_ms: 0,
    active_workers: 0, in_flight_processes: 0)).accepted).to_be(false)
val beyond = admit_bounded_process(BoundedProcessAdmissionV2(
    policy: policy, requested_timeout_ms: 1001,
    active_workers: 0, in_flight_processes: 0))
expect(beyond.code).to_equal(ProcessSafetyCodeV1.TimeoutLimitReached)
```

</details>

#### POLICY-MCI-PROC rejects invalid policy and negative in-flight state

- POLICY-MCI-PROC rejects invalid policy and negative in-flight state


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("POLICY-MCI-PROC rejects invalid policy and negative in-flight state")
val invalid_policy = BoundedProcessPolicyV2(
    max_timeout_ms: 1000, max_in_flight: 0)
expect(admit_bounded_process(BoundedProcessAdmissionV2(
    policy: invalid_policy, requested_timeout_ms: 1000,
    active_workers: 0, in_flight_processes: 0)).code).to_equal(ProcessSafetyCodeV1.InvalidCapacity)
val valid_policy = BoundedProcessPolicyV2(
    max_timeout_ms: 1000, max_in_flight: 1)
expect(admit_bounded_process(BoundedProcessAdmissionV2(
    policy: valid_policy, requested_timeout_ms: 1000,
    active_workers: 0, in_flight_processes: -1)).accepted).to_be(false)
```

</details>

#### REQ-MCI-009 binds termination to lease identity and rejects PID reuse forged group and replay

- REQ-MCI-009 binds termination to lease identity and rejects PID reuse forged group and replay
   - Expected: stale.code equals `ProcessSafetyCodeV1.InvalidTransition`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-MCI-009 binds termination to lease identity and rejects PID reuse forged group and replay")
val slot = "slot-7"
val token = process_owner_lease_token_v4(1, 2, 3, 4, 41, 41, slot)
val lease = ProcessOwnerLeaseV4(run_id: 1, execution_id: 2, generation: 3,
    start_identity: 4, pid: 41, process_group_id: 41,
    admission_slot_token: slot, lease_token: token)
val running = BoundedExecutionV4(
    state: BoundedExecutionStateV4.Running, lease: lease, transition_sequence: 9)
val forged = ProcessOwnerLeaseV4(run_id: 1, execution_id: 2, generation: 3,
    start_identity: 4, pid: 41, process_group_id: 99,
    admission_slot_token: slot, lease_token: token)
expect(transition_bounded_execution_v4(running,
    BoundedExecutionEventV4.ReachTimeout, forged, 9).accepted).to_be(false)
val reused = ProcessOwnerLeaseV4(run_id: 1, execution_id: 2, generation: 3,
    start_identity: 5, pid: 41, process_group_id: 41,
    admission_slot_token: slot, lease_token: token)
expect(transition_bounded_execution_v4(running,
    BoundedExecutionEventV4.ReachTimeout, reused, 9).accepted).to_be(false)
val stale = transition_bounded_execution_v4(running,
    BoundedExecutionEventV4.RequestCancel, lease, 8)
expect(stale.code).to_equal(ProcessSafetyCodeV1.InvalidTransition)
```

</details>

#### REQ-MCI-009 requires termination confirmation and registered reap before terminal state

- REQ-MCI-009 requires termination confirmation and registered reap before terminal state
   - Expected: requested.after equals `BoundedExecutionStateV4.TerminationRequested`
   - Expected: pending.after equals `BoundedExecutionStateV4.ReapPending`
   - Expected: complete.after equals `BoundedExecutionStateV4.Completed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-MCI-009 requires termination confirmation and registered reap before terminal state")
val slot = "slot-8"
val token = process_owner_lease_token_v4(2, 3, 4, 5, 51, 51, slot)
val lease = ProcessOwnerLeaseV4(run_id: 2, execution_id: 3, generation: 4,
    start_identity: 5, pid: 51, process_group_id: 51,
    admission_slot_token: slot, lease_token: token)
val running = BoundedExecutionV4(
    state: BoundedExecutionStateV4.Running, lease: lease, transition_sequence: 0)
val requested = transition_bounded_execution_v4(
    running, BoundedExecutionEventV4.ReachTimeout, lease, 0)
expect(requested.after).to_equal(BoundedExecutionStateV4.TerminationRequested)
val terminating = BoundedExecutionV4(
    state: requested.after, lease: lease, transition_sequence: requested.next_sequence)
val pending = transition_bounded_execution_v4(
    terminating, BoundedExecutionEventV4.ConfirmTermination, lease, 1)
expect(pending.after).to_equal(BoundedExecutionStateV4.ReapPending)
expect(pending.reap_intent).to_be(true)
val reaping = BoundedExecutionV4(
    state: pending.after, lease: lease, transition_sequence: pending.next_sequence)
val complete = transition_bounded_execution_v4(
    reaping, BoundedExecutionEventV4.AcknowledgeRegisteredReap, lease, 2)
expect(complete.after).to_equal(BoundedExecutionStateV4.Completed)
```

</details>

#### REQ-MCI-009 policy-model reserves the last slot and rejects competing stale reservation

- REQ-MCI-009 policy-model reserves the last slot and rejects competing stale reservation
   - Expected: reserve_process_slot_v4(committed).code equals `ProcessSafetyCodeV1.InFlightLimitReached`
   - Expected: release_process_slot_v4(committed, 2, winner.slot_token).next_reserved equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("REQ-MCI-009 policy-model reserves the last slot and rejects competing stale reservation")
val pool = ProcessSlotPoolV4(max_in_flight: 2, reserved: 1, generation: 6)
val winner = reserve_process_slot_v4(pool)
expect(winner.accepted).to_be(true)
val committed = ProcessSlotPoolV4(max_in_flight: 2,
    reserved: winner.next_reserved, generation: 6)
expect(reserve_process_slot_v4(committed).code).to_equal(ProcessSafetyCodeV1.InFlightLimitReached)
expect(release_process_slot_v4(committed, 2, winner.slot_token).next_reserved).to_equal(1)
expect(release_process_slot_v4(committed, 1, winner.slot_token).accepted).to_be(false)
```

</details>

#### NFR-MCI-003 incrementally admits exact capture chunks and rejects plus one without mutation

- NFR-MCI-003 incrementally admits exact capture chunks and rejects plus one without mutation
   - Expected: exact.next.stdout_bytes equals `16`
   - Expected: exact.receipt_token.len() equals `64`
   - Expected: overflow.code equals `ProcessSafetyCodeV1.CaptureLimitReached`
   - Expected: overflow.next.stdout_bytes equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("NFR-MCI-003 incrementally admits exact capture chunks and rejects plus one without mutation")
val initial = CaptureAccumulatorV4(max_stdout_bytes: 16, max_stderr_bytes: 8,
    stdout_bytes: 15, stderr_bytes: 7, lease_token: "lease-hash", sequence: 3)
val exact = append_capture_chunk_v4(initial, 1, 1)
expect(exact.accepted).to_be(true)
expect(exact.next.stdout_bytes).to_equal(16)
expect(exact.receipt_token.len()).to_equal(64)
val overflow = append_capture_chunk_v4(exact.next, 1, 0)
expect(overflow.code).to_equal(ProcessSafetyCodeV1.CaptureLimitReached)
expect(overflow.next.stdout_bytes).to_equal(16)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/mission_critical/bounded_process_policy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering bounded mission-critical process policy.
- bounded mission-critical process policy

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-MCI-009`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4209e309a285a0d5a9fd78c0d5399cfc0779ad98736cbce62e8f10ea703952dc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4209e309a285a0d5a9fd78c0d5399cfc0779ad98736cbce62e8f10ea703952dc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4209e309a285a0d5a9fd78c0d5399cfc0779ad98736cbce62e8f10ea703952dc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/mission_critical/bounded_process_policy_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/mission_critical/bounded_process_policy_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/mission_critical/bounded_process_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/mission_critical/bounded_process_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/mission_critical/bounded_process_policy_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/mission_critical/bounded_process_policy_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'POLICY-MCI-PROC rejects non-positive signal and wait targets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/mission_critical/bounded_process_policy_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'POLICY-MCI-PROC admits exact worker and queue boundaries' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/mission_critical/bounded_process_policy_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'POLICY-MCI-PROC rejects work beyond the fixed queue' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
