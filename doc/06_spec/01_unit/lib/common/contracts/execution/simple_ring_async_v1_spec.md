# Simple Ring Async V1 Specification

> Tests covering SimpleRing async V1 metadata contracts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Ring Async V1 Specification

## Scenarios

### SimpleRing async V1 metadata contracts

#### publishes stable version and canonical provider texts

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- publishes stable version and canonical provider texts
   - Expected: SIMPLE_RING_ASYNC_V1 equals `1`
   - Expected: simple_ring_async_v1_version() equals `SIMPLE_RING_ASYNC_V1`
   - Expected: simple_ring_async_v1_canonical_text() equals `simple-ring-async-v1`
   - Expected: ring_mapping_grade_canonical_text(RingMappingGrade.Direct) equals `direct`
   - Expected: ring_mapping_grade_canonical_text(RingMappingGrade.Translated) equals `translated`
   - Expected: ring_mapping_grade_canonical_text(RingMappingGrade.Software) equals `software`
   - Expected: ring_mapping_grade_canonical_text(RingMappingGrade.Emulated) equals `emulated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("publishes stable version and canonical provider texts")
expect(SIMPLE_RING_ASYNC_V1).to_equal(1)
expect(simple_ring_async_v1_version()).to_equal(SIMPLE_RING_ASYNC_V1)
expect(simple_ring_async_v1_canonical_text()).to_equal("simple-ring-async-v1")
expect(ring_mapping_grade_canonical_text(RingMappingGrade.Direct)).to_equal("direct")
expect(ring_mapping_grade_canonical_text(RingMappingGrade.Translated)).to_equal("translated")
expect(ring_mapping_grade_canonical_text(RingMappingGrade.Software)).to_equal("software")
expect(ring_mapping_grade_canonical_text(RingMappingGrade.Emulated)).to_equal("emulated")
```

</details>

#### validates the nonzero generation and stable token identity

- validates the nonzero generation and stable token identity
   - Expected: initial.value equals `1u64`
   - Expected: ring_generation_validate(initial).error equals `RingContractError.None`
   - Expected: ring_token_validate(valid_token()).error equals `RingContractError.None`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("validates the nonzero generation and stable token identity")
val initial = ring_generation_initial()
expect(initial.value).to_equal(1u64)
expect(ring_generation_validate(initial).error).to_equal(RingContractError.None)
expect(ring_generation_validate(RingGeneration(value: 0u64)).error).to_equal(
    RingContractError.InvalidGeneration)
expect(ring_token_validate(valid_token()).error).to_equal(RingContractError.None)
expect(ring_token_validate(RingToken(
    ring_id: 0u64, slot: 0u64, generation: initial)).error).to_equal(
    RingContractError.InvalidRingId)
expect(ring_token_validate(RingToken(
    ring_id: 7u64, slot: 0u64, generation: RingGeneration(value: 0u64))).error).to_equal(
    RingContractError.InvalidGeneration)
```

</details>

#### keeps every admission outcome explicit and internally consistent

- keeps every admission outcome explicit and internally consistent
   - Expected: ring_admission_validate(admitted).error equals `RingContractError.None`
   - Expected: ring_admission_status_canonical_text(RingAdmissionStatus.Admitted) equals `admitted`
   - Expected: ring_admission_status_canonical_text(RingAdmissionStatus.Full) equals `full`
   - Expected: ring_admission_status_canonical_text(RingAdmissionStatus.Rejected) equals `rejected`
   - Expected: ring_admission_status_canonical_text(RingAdmissionStatus.Fallback) equals `fallback`
   - Expected: ring_admission_validate(full).error equals `RingContractError.None`
   - Expected: ring_admission_validate(rejected).error equals `RingContractError.None`
   - Expected: ring_admission_validate(fallback).error equals `RingContractError.None`


<details>
<summary>Executable SSpec</summary>

Runnable source: 55 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps every admission outcome explicit and internally consistent")
val admitted = RingAdmission(
    status: RingAdmissionStatus.Admitted,
    token: valid_token(),
    admitted_count: 1
)
expect(ring_admission_validate(admitted).error).to_equal(RingContractError.None)
expect(ring_admission_status_canonical_text(RingAdmissionStatus.Admitted)).to_equal("admitted")
expect(ring_admission_status_canonical_text(RingAdmissionStatus.Full)).to_equal("full")
expect(ring_admission_status_canonical_text(RingAdmissionStatus.Rejected)).to_equal("rejected")
expect(ring_admission_status_canonical_text(RingAdmissionStatus.Fallback)).to_equal("fallback")

val missing_token = RingAdmission(
    status: RingAdmissionStatus.Admitted,
    token: nil,
    admitted_count: 1
)
expect(ring_admission_validate(missing_token).error).to_equal(
    RingContractError.InvalidAdmission)
val zero_admitted_count = RingAdmission(
    status: RingAdmissionStatus.Admitted,
    token: valid_token(),
    admitted_count: 0
)
expect(ring_admission_validate(zero_admitted_count).error).to_equal(
    RingContractError.InvalidAdmission)
val full = RingAdmission(status: RingAdmissionStatus.Full, token: nil, admitted_count: 0)
expect(ring_admission_validate(full).error).to_equal(RingContractError.None)
val rejected = RingAdmission(status: RingAdmissionStatus.Rejected, token: nil, admitted_count: 0)
expect(ring_admission_validate(rejected).error).to_equal(RingContractError.None)
val fallback = RingAdmission(status: RingAdmissionStatus.Fallback, token: nil, admitted_count: 0)
expect(ring_admission_validate(fallback).error).to_equal(RingContractError.None)
val hidden_token = RingAdmission(
    status: RingAdmissionStatus.Full,
    token: valid_token(),
    admitted_count: 0
)
expect(ring_admission_validate(hidden_token).error).to_equal(
    RingContractError.InvalidAdmission)
val hidden_count = RingAdmission(
    status: RingAdmissionStatus.Fallback,
    token: nil,
    admitted_count: 1
)
expect(ring_admission_validate(hidden_count).error).to_equal(
    RingContractError.InvalidAdmission)
val invalid_admitted_token = RingAdmission(
    status: RingAdmissionStatus.Admitted,
    token: RingToken(
        ring_id: 0u64, slot: 0u64, generation: ring_generation_initial()),
    admitted_count: 1
)
expect(ring_admission_validate(invalid_admitted_token).error).to_equal(
    RingContractError.InvalidRingId)
```

</details>

#### requires exactly one typed terminal completion shape

- requires exactly one typed terminal completion shape
   - Expected: ring_completion_validate(success).error equals `RingContractError.None`
   - Expected: ring_completion_validate(failure).error equals `RingContractError.None`
   - Expected: ring_completion_validate(cancelled).error equals `RingContractError.None`
   - Expected: ring_terminal_kind_canonical_text(RingTerminalKind.Success) equals `success`
   - Expected: ring_terminal_kind_canonical_text(RingTerminalKind.Failure) equals `failure`
   - Expected: ring_terminal_kind_canonical_text(RingTerminalKind.Cancelled) equals `cancelled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 64 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires exactly one typed terminal completion shape")
val success = RingCompletion<i64>(
    token: valid_token(), task_key: 3u64, kind: RingTerminalKind.Success,
    value: 42, error: ""
)
expect(ring_completion_validate(success).error).to_equal(RingContractError.None)
val failure = RingCompletion<i64>(
    token: valid_token(), task_key: 3u64, kind: RingTerminalKind.Failure,
    value: nil, error: "io-failed"
)
expect(ring_completion_validate(failure).error).to_equal(RingContractError.None)
val cancelled = RingCompletion<i64>(
    token: valid_token(), task_key: 3u64, kind: RingTerminalKind.Cancelled,
    value: nil, error: "cancelled"
)
expect(ring_completion_validate(cancelled).error).to_equal(RingContractError.None)
expect(ring_terminal_kind_canonical_text(RingTerminalKind.Success)).to_equal("success")
expect(ring_terminal_kind_canonical_text(RingTerminalKind.Failure)).to_equal("failure")
expect(ring_terminal_kind_canonical_text(RingTerminalKind.Cancelled)).to_equal("cancelled")

val duplicate_payload = RingCompletion<i64>(
    token: valid_token(), task_key: 3u64, kind: RingTerminalKind.Failure,
    value: 1, error: "io-failed"
)
expect(ring_completion_validate(duplicate_payload).error).to_equal(
    RingContractError.InvalidCompletion)
val missing_success_value = RingCompletion<i64>(
    token: valid_token(), task_key: 3u64, kind: RingTerminalKind.Success,
    value: nil, error: ""
)
expect(ring_completion_validate(missing_success_value).error).to_equal(
    RingContractError.InvalidCompletion)
val anonymous_cancel = RingCompletion<i64>(
    token: valid_token(), task_key: 3u64, kind: RingTerminalKind.Cancelled,
    value: nil, error: " "
)
expect(ring_completion_validate(anonymous_cancel).error).to_equal(
    RingContractError.InvalidCompletion)
val anonymous_completion = RingCompletion<i64>(
    token: valid_token(), task_key: 0u64, kind: RingTerminalKind.Success,
    value: 1, error: ""
)
expect(ring_completion_validate(anonymous_completion).error).to_equal(
    RingContractError.InvalidTaskKey)
val invalid_completion_token = RingCompletion<i64>(
    token: RingToken(
        ring_id: 0u64, slot: 0u64, generation: ring_generation_initial()),
    task_key: 3u64, kind: RingTerminalKind.Success, value: 1, error: ""
)
expect(ring_completion_validate(invalid_completion_token).error).to_equal(
    RingContractError.InvalidRingId)
val success_with_error = RingCompletion<i64>(
    token: valid_token(), task_key: 3u64, kind: RingTerminalKind.Success,
    value: 1, error: "unexpected"
)
expect(ring_completion_validate(success_with_error).error).to_equal(
    RingContractError.InvalidCompletion)
val missing_failure_error = RingCompletion<i64>(
    token: valid_token(), task_key: 3u64, kind: RingTerminalKind.Failure,
    value: nil, error: ""
)
expect(ring_completion_validate(missing_failure_error).error).to_equal(
    RingContractError.InvalidCompletion)
```

</details>

#### validates caller-owned and registered payload lease shapes exhaustively

- validates caller-owned and registered payload lease shapes exhaustively


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("validates caller-owned and registered payload lease shapes exhaustively")
val caller_owned = RingPayloadLease(
    ownership: RingPayloadOwnership.CallerOwned,
    owner_id: 8u64,
    handle: 0u64,
    generation: ring_generation_initial(),
    byte_length: 0u64
)
expect(ring_payload_lease_validate(caller_owned).error).to_equal(
    RingContractError.None)
val registered = RingPayloadLease(
    ownership: RingPayloadOwnership.RegisteredLease,
    owner_id: 8u64,
    handle: 19u64,
    generation: ring_generation_initial(),
    byte_length: 4096u64
)
expect(ring_payload_lease_validate(registered).error).to_equal(
    RingContractError.None)

var anonymous_owner = caller_owned
anonymous_owner.owner_id = 0u64
expect(ring_payload_lease_validate(anonymous_owner).error).to_equal(
    RingContractError.InvalidPayloadLease)
var caller_with_handle = caller_owned
caller_with_handle.handle = 1u64
expect(ring_payload_lease_validate(caller_with_handle).error).to_equal(
    RingContractError.InvalidPayloadLease)
var caller_with_length = caller_owned
caller_with_length.byte_length = 1u64
expect(ring_payload_lease_validate(caller_with_length).error).to_equal(
    RingContractError.InvalidPayloadLease)
var registered_without_handle = registered
registered_without_handle.handle = 0u64
expect(ring_payload_lease_validate(registered_without_handle).error).to_equal(
    RingContractError.InvalidPayloadLease)
var registered_without_length = registered
registered_without_length.byte_length = 0u64
expect(ring_payload_lease_validate(registered_without_length).error).to_equal(
    RingContractError.InvalidPayloadLease)
var stale_lease = registered
stale_lease.generation = RingGeneration(value: 0u64)
expect(ring_payload_lease_validate(stale_lease).error).to_equal(
    RingContractError.InvalidPayloadLease)
```

</details>

#### validates complete operation metadata and its payload ownership

- validates complete operation metadata and its payload ownership


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("validates complete operation metadata and its payload ownership")
val lease = RingPayloadLease(
    ownership: RingPayloadOwnership.RegisteredLease,
    owner_id: 8u64, handle: 19u64,
    generation: ring_generation_initial(), byte_length: 4096u64)
val metadata = RingOperationMetadata(
    resource_handle: 71u64, task_key: 72u64, priority: 3,
    deadline: 1000u64, dependency_value: 9u64, flags: 5u64,
    payload_lease: lease, trace_id: 73u64)
expect(ring_operation_metadata_validate(metadata).error).to_equal(
    RingContractError.None)
var anonymous_task = metadata
anonymous_task.task_key = 0u64
expect(ring_operation_metadata_validate(anonymous_task).error).to_equal(
    RingContractError.InvalidOperationMetadata)
var invalid_priority = metadata
invalid_priority.priority = -1
expect(ring_operation_metadata_validate(invalid_priority).error).to_equal(
    RingContractError.InvalidOperationMetadata)
var missing_trace = metadata
missing_trace.trace_id = 0u64
expect(ring_operation_metadata_validate(missing_trace).error).to_equal(
    RingContractError.InvalidOperationMetadata)
var invalid_lease = metadata
invalid_lease.payload_lease.handle = 0u64
expect(ring_operation_metadata_validate(invalid_lease).error).to_equal(
    RingContractError.InvalidOperationMetadata)
```

</details>

#### validates typed frame and context metadata before polling

- validates typed frame and context metadata before polling
   - Expected: async_task_frame_validate(valid_frame(nil)).error equals `RingContractError.None`
   - Expected: task_context_validate(valid_context()).error equals `RingContractError.None`


<details>
<summary>Executable SSpec</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("validates typed frame and context metadata before polling")
expect(async_task_frame_validate(valid_frame(valid_token())).error).to_equal(
    RingContractError.None)
expect(async_task_frame_validate(valid_frame(nil)).error).to_equal(RingContractError.None)
var bad_frame = valid_frame(nil)
bad_frame.profile_fingerprint = " "
expect(async_task_frame_validate(bad_frame).error).to_equal(
    RingContractError.InvalidProfileFingerprint)
var missing_frame_id = valid_frame(nil)
missing_frame_id.task_id = 0u64
expect(async_task_frame_validate(missing_frame_id).error).to_equal(
    RingContractError.InvalidTaskFrame)
var missing_cancel_key = valid_frame(nil)
missing_cancel_key.cancellation_key = 0u64
expect(async_task_frame_validate(missing_cancel_key).error).to_equal(
    RingContractError.InvalidTaskFrame)
var negative_state = valid_frame(nil)
negative_state.state = -1
expect(async_task_frame_validate(negative_state).error).to_equal(
    RingContractError.InvalidTaskFrame)
var negative_priority = valid_frame(nil)
negative_priority.priority = -1
expect(async_task_frame_validate(negative_priority).error).to_equal(
    RingContractError.InvalidTaskFrame)
var blank_trace = valid_frame(nil)
blank_trace.trace = " "
expect(async_task_frame_validate(blank_trace).error).to_equal(
    RingContractError.InvalidTaskFrame)
var detached_without_supervisor = valid_frame(nil)
detached_without_supervisor.detached = true
expect(async_task_frame_validate(detached_without_supervisor).error).to_equal(
    RingContractError.InvalidTaskFrame)
detached_without_supervisor.supervisor_capability = 77u64
expect(async_task_frame_validate(detached_without_supervisor).error).to_equal(
    RingContractError.None)
val stale_frame = valid_frame(RingToken(
    ring_id: 7u64, slot: 0u64, generation: RingGeneration(value: 0u64)))
expect(async_task_frame_validate(stale_frame).error).to_equal(
    RingContractError.InvalidGeneration)

expect(task_context_validate(valid_context()).error).to_equal(RingContractError.None)
var exhausted = valid_context()
exhausted.budget = 0
expect(task_context_validate(exhausted).error).to_equal(
    RingContractError.InvalidTaskContext)
var anonymous_context = valid_context()
anonymous_context.executor_id = 0u64
expect(task_context_validate(anonymous_context).error).to_equal(
    RingContractError.InvalidTaskContext)
var missing_wake_key = valid_context()
missing_wake_key.wake_key = 0u64
expect(task_context_validate(missing_wake_key).error).to_equal(
    RingContractError.InvalidTaskContext)
var expired = valid_context()
expired.deadline = 49u64
expect(task_context_validate(expired).error).to_equal(
    RingContractError.InvalidTaskContext)
var blank_profile = valid_context()
blank_profile.profile_fingerprint = ""
expect(task_context_validate(blank_profile).error).to_equal(
    RingContractError.InvalidProfileFingerprint)
```

</details>

#### distinguishes Ready values from Pending exact wake tokens

- distinguishes Ready values from Pending exact wake tokens
   - Expected: "ready predicate" equals `ready predicate`
   - Expected: "ready predicate" equals `incorrect`
   - Expected: "pending predicate" equals `pending predicate`
   - Expected: "pending predicate" equals `incorrect`
   - Expected: task_poll_result_validate(ready).error equals `RingContractError.None`
   - Expected: task_poll_result_validate(pending).error equals `RingContractError.None`
   - Expected: token.ring_id equals `7u64`
   - Expected: token.slot equals `0u64`
   - Expected: "pending token" equals `missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("distinguishes Ready values from Pending exact wake tokens")
val ready = TaskPollResult<i64>.Ready(41)
val pending = TaskPollResult<i64>.Pending(valid_token())
match ready:
    case TaskPollResult.Ready(value): expect(value).to_equal(41)
    case TaskPollResult.Pending(_): expect("ready result").to_equal("pending")
match pending:
    case TaskPollResult.Ready(_): expect("pending result").to_equal("ready")
    case TaskPollResult.Pending(token): expect(token.ring_id).to_equal(7u64)
if task_poll_result_is_ready(ready) and not task_poll_result_is_pending(ready):
    expect("ready predicate").to_equal("ready predicate")
else:
    expect("ready predicate").to_equal("incorrect")
if task_poll_result_is_pending(pending) and not task_poll_result_is_ready(pending):
    expect("pending predicate").to_equal("pending predicate")
else:
    expect("pending predicate").to_equal("incorrect")
expect(task_poll_result_validate(ready).error).to_equal(RingContractError.None)
expect(task_poll_result_validate(pending).error).to_equal(RingContractError.None)
expect(task_poll_result_wait_token(ready)).to_be_nil()
if val token = task_poll_result_wait_token(pending):
    expect(token.ring_id).to_equal(7u64)
    expect(token.slot).to_equal(0u64)
else:
    expect("pending token").to_equal("missing")
val stale_pending = TaskPollResult<i64>.Pending(RingToken(
    ring_id: 7u64, slot: 0u64, generation: RingGeneration(value: 0u64)))
expect(task_poll_result_validate(stale_pending).error).to_equal(
    RingContractError.InvalidGeneration)
```

</details>

#### polls a real stackless task implementation without waiting

- polls a real stackless task implementation without waiting
   - Expected: task_poll_result_validate(pending).error equals `RingContractError.None`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("polls a real stackless task implementation without waiting")
val task = OnePollTask(value: 73)
var pending_frame = valid_frame(nil)
pending_frame.state = 0
val pending = task.poll(pending_frame, valid_context())
expect(task_poll_result_is_pending(pending)).to_be(true)
expect(task_poll_result_validate(pending).error).to_equal(RingContractError.None)

var ready_frame = valid_frame(nil)
ready_frame.state = 1
val ready = task.poll(ready_frame, valid_context())
match ready:
    case TaskPollResult.Ready(value): expect(value).to_equal(73)
    case TaskPollResult.Pending(_): expect("ready").to_equal("pending")
```

</details>

#### validates causal trace identity and operation tokens

- validates causal trace identity and operation tokens
   - Expected: async_trace_event_validate(event).error equals `RingContractError.None`
   - Expected: async_trace_event_validate(task_event).error equals `RingContractError.None`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("validates causal trace identity and operation tokens")
val event = AsyncTraceEvent(
    kind: AsyncTraceEventKind.ProviderComplete,
    task_id: 11u64,
    parent_task_id: 2u64,
    ring_id: 7u64,
    operation_token: valid_token(),
    provider_id: 5u64,
    trace_id: 91u64,
    sequence: 3u64
)
expect(async_trace_event_validate(event).error).to_equal(RingContractError.None)
var task_event = event
task_event.kind = AsyncTraceEventKind.TaskSpawn
task_event.operation_token = nil
expect(async_trace_event_validate(task_event).error).to_equal(RingContractError.None)

var missing_task = event
missing_task.task_id = 0u64
expect(async_trace_event_validate(missing_task).error).to_equal(
    RingContractError.InvalidTaskFrame)
var missing_trace = event
missing_trace.trace_id = 0u64
expect(async_trace_event_validate(missing_trace).error).to_equal(
    RingContractError.InvalidTaskFrame)
var missing_sequence = event
missing_sequence.sequence = 0u64
expect(async_trace_event_validate(missing_sequence).error).to_equal(
    RingContractError.InvalidTaskFrame)
var invalid_token = event
invalid_token.operation_token = RingToken(
    ring_id: 0u64, slot: 0u64, generation: ring_generation_initial())
expect(async_trace_event_validate(invalid_token).error).to_equal(
    RingContractError.InvalidRingId)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/contracts/execution/simple_ring_async_v1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleRing async V1 metadata contracts.
- SimpleRing async V1 metadata contracts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `c0631a5289d2d6244ea5aa93ff4e5e5c529dc0ee65d9174b454a0c1a8aace71c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c0631a5289d2d6244ea5aa93ff4e5e5c529dc0ee65d9174b454a0c1a8aace71c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c0631a5289d2d6244ea5aa93ff4e5e5c529dc0ee65d9174b454a0c1a8aace71c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/contracts/execution/simple_ring_async_v1_spec.spl
mirror: doc/06_spec/01_unit/lib/common/contracts/execution/simple_ring_async_v1_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/contracts/execution/simple_ring_async_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/contracts/execution/simple_ring_async_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/contracts/execution/simple_ring_async_v1_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/contracts/execution/simple_ring_async_v1_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes stable version and canonical provider texts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/contracts/execution/simple_ring_async_v1_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates the nonzero generation and stable token identity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/contracts/execution/simple_ring_async_v1_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every admission outcome explicit and internally consistent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
