# Simple Ring Specification

> Tests covering SimpleRing fixed-capacity lifecycle.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Ring Specification

## Scenarios

### SimpleRing fixed-capacity lifecycle

#### reserves and commits batches with all-or-nothing validation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reserves and commits batches with all-or-nothing validation
   - Expected: value.occupancy() equals `2u64`
   - Expected: value.telemetry().batches equals `1u64`
   - Expected: value.telemetry().batch_items equals `2u64`
   - Expected: value.occupancy() equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reserves and commits batches with all-or-nothing validation")
val value = ring(3)
match value.commit_batch(7u64, [10u64, 20u64], [101, 202], RingBatchPolicy.AllOrNothing):
    case Ok(receipt): expect(receipt.committed).to_equal(2u64)
    case Err(_): fail("batch commit failed")
expect(value.occupancy()).to_equal(2u64)
expect(value.telemetry().batches).to_equal(1u64)
expect(value.telemetry().batch_items).to_equal(2u64)
match value.commit_batch(7u64, [30u64, 40u64], [303, 404], RingBatchPolicy.AllOrNothing):
    case Err(error): expect(error).to_equal(SimpleRingError.Full)
    case Ok(_): fail("partial batch was admitted")
expect(value.occupancy()).to_equal(2u64)
```

</details>

#### rejects invalid construction and wrong mutable owner

- rejects invalid construction and wrong mutable owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects invalid construction and wrong mutable owner")
match SimpleRing<i64, i64>.create(0u64, 7u64, 1):
    case Err(error): expect(error).to_equal(SimpleRingError.InvalidRingId)
    case Ok(_): fail("zero ring id accepted")
match SimpleRing<i64, i64>.create(1u64, 0u64, 1):
    case Err(error): expect(error).to_equal(SimpleRingError.InvalidOwner)
    case Ok(_): fail("zero owner accepted")
match SimpleRing<i64, i64>.create(1u64, 7u64, 0):
    case Err(error): expect(error).to_equal(SimpleRingError.InvalidCapacity)
    case Ok(_): fail("zero capacity accepted")
val value = ring(1)
match value.reserve(8u64, 1u64):
    case Err(error): expect(error).to_equal(SimpleRingError.WrongOwner)
    case Ok(_): fail("foreign owner reserved")
```

</details>

#### is bounded and advances free indices through release without scanning

- is bounded and advances free indices through release without scanning
   - Expected: value.occupancy() equals `2u64`
   - Expected: value.high_water() equals `2u64`
   - Expected: value.telemetry().full_events equals `1u64`
   - Expected: reused.token.slot equals `first.token.slot`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is bounded and advances free indices through release without scanning")
val value = ring(2)
val first = reservation(value, 10u64)
val second = reservation(value, 20u64)
expect(value.occupancy()).to_equal(2u64)
expect(value.high_water()).to_equal(2u64)
expect(value.is_full()).to_be(true)
match value.reserve(7u64, 30u64):
    case Err(error): expect(error).to_equal(SimpleRingError.Full)
    case Ok(_): fail("full ring admitted")
expect(value.telemetry().full_events).to_equal(1u64)
match value.release(7u64, first):
    case Ok(_): expect(value.occupancy()).to_equal(1u64)
    case Err(_): fail("release failed")
val reused = reservation(value, 30u64)
expect(reused.token.slot).to_equal(first.token.slot)
expect(reused.token.generation.value).to_be_greater_than(first.token.generation.value)
match value.release(7u64, second):
    case Ok(_): expect(value.occupancy()).to_equal(1u64)
    case Err(_): fail("second release failed")
```

</details>

#### keeps provider submission and completion FIFO across wrap

- keeps provider submission and completion FIFO across wrap
   - Expected: first_submission.operation equals `101`
   - Expected: second_submission.operation equals `202`
   - Expected: first_completion.task_key equals `10u64`
   - Expected: result equals `1001`
   - Expected: second_completion.task_key equals `20u64`
   - Expected: result equals `2002`
   - Expected: value.occupancy() equals `0u64`
   - Expected: value.telemetry().provider_takes equals `2u64`
   - Expected: value.telemetry().completions equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 56 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps provider submission and completion FIFO across wrap")
val value = ring(2)
val first = reservation(value, 10u64)
val second = reservation(value, 20u64)
match value.commit(7u64, first, 101):
    case Ok(_): ()
    case Err(_): fail("first commit failed")
match value.commit(7u64, second, 202):
    case Ok(_): ()
    case Err(_): fail("second commit failed")
val submitted_one = match value.provider_take(1):
    case Ok(item): item
    case Err(_): fail("first provider take failed")
if val first_submission = submitted_one:
    expect(first_submission.operation).to_equal(101)
    match value.complete_success(first_submission.token, 1001):
        case Ok(_): ()
        case Err(_): fail("first completion failed")
else:
    fail("first provider take was empty")
val submitted_two = match value.provider_take(1):
    case Ok(item): item
    case Err(_): fail("second provider take failed")
if val second_submission = submitted_two:
    expect(second_submission.operation).to_equal(202)
    match value.complete_success(second_submission.token, 2002):
        case Ok(_): ()
        case Err(_): fail("second completion failed")
else:
    fail("second provider take was empty")
val complete_one = match value.take_completion(7u64):
    case Ok(item): item
    case Err(_): fail("first completion take failed")
if val first_completion = complete_one:
    expect(first_completion.task_key).to_equal(10u64)
    if val result = first_completion.value:
        expect(result).to_equal(1001)
    else:
        fail("missing first completion value")
else:
    fail("first completion queue empty")
val complete_two = match value.take_completion(7u64):
    case Ok(item): item
    case Err(_): fail("second completion take failed")
if val second_completion = complete_two:
    expect(second_completion.task_key).to_equal(20u64)
    if val result = second_completion.value:
        expect(result).to_equal(2002)
    else:
        fail("missing second completion value")
else:
    fail("second completion queue empty")
expect(value.occupancy()).to_equal(0u64)
expect(value.telemetry().provider_takes).to_equal(2u64)
expect(value.telemetry().completions).to_equal(2u64)
```

</details>

#### rejects duplicate and stale terminal attempts and records them

- rejects duplicate and stale terminal attempts and records them
   - Expected: value.telemetry().duplicate_rejects equals `1u64`
   - Expected: value.telemetry().stale_rejects equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 29 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects duplicate and stale terminal attempts and records them")
val value = ring(1)
val held = reservation(value, 10u64)
match value.commit(7u64, held, 1):
    case Ok(_): ()
    case Err(_): fail("commit failed")
val submission = match value.provider_take(1):
    case Ok(item): item
    case Err(_): fail("provider take failed")
if val item = submission:
    match value.complete_failure(item.token, "device-fault"):
        case Ok(_): ()
        case Err(_): fail("failure completion failed")
    match value.complete_success(item.token, 2):
        case Err(error): expect(error).to_equal(SimpleRingError.TerminalAlreadyPublished)
        case Ok(_): fail("duplicate terminal accepted")
    val complete = match value.take_completion(7u64):
        case Ok(item): item
        case Err(_): fail("take completion failed")
    if complete == nil:
        fail("completion missing")
    match value.complete_cancelled(item.token, "late"):
        case Err(error): expect(error).to_equal(SimpleRingError.StaleToken)
        case Ok(_): fail("stale terminal accepted")
else:
    fail("provider take empty")
expect(value.telemetry().duplicate_rejects).to_equal(1u64)
expect(value.telemetry().stale_rejects).to_equal(1u64)
```

</details>

#### distinguishes cancellation before commit from provider cancellation

- distinguishes cancellation before commit from provider cancellation
   - Expected: error equals `SimpleRingError.CancellationAlreadyRequested`
   - Expected: value.telemetry().cancellations equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("distinguishes cancellation before commit from provider cancellation")
val value = ring(2)
val reserved = reservation(value, 10u64)
match value.cancel(7u64, reserved.token):
    case RingCancelOutcome.CancelledBeforeCommit(token): expect(token.slot).to_equal(reserved.token.slot)
    case _: fail("reserved cancellation had wrong outcome")
val committed = reservation(value, 20u64)
match value.commit(7u64, committed, 20):
    case Ok(_): ()
    case Err(_): fail("commit failed")
match value.cancel(7u64, committed.token):
    case RingCancelOutcome.ProviderCancelRequested(token): expect(token.slot).to_equal(committed.token.slot)
    case _: fail("committed cancellation had wrong outcome")
match value.cancel(7u64, committed.token):
    case RingCancelOutcome.CancelRejected(error):
        expect(error).to_equal(SimpleRingError.CancellationAlreadyRequested)
    case _: fail("duplicate cancellation request was accepted")
val submission = match value.provider_take(1):
    case Ok(Some(item)): item
    case Ok(nil): fail("cancel-requested submission missing")
    case Err(_): fail("provider take failed")
expect(submission.cancel_requested).to_be(true)
match value.complete_success(submission.token, 20):
    case Err(error): expect(error).to_equal(SimpleRingError.CancellationRequired)
    case Ok(_): fail("success won after cancellation linearized")
match value.complete_cancelled(submission.token, "owner requested"):
    case Ok(_): ()
    case Err(_): fail("cancel terminal failed")
expect(value.telemetry().cancellations).to_equal(2u64)
```

</details>

#### validates registered payload ownership and carries the lease to the provider

- validates registered payload ownership and carries the lease to the provider
   - Expected: submission.payload_lease.handle equals `55u64`
   - Expected: submission.payload_lease.generation.value equals `3u64`
   - Expected: submission.payload_lease.byte_length equals `4096u64`
   - Expected: submission.metadata.resource_handle equals `66u64`
   - Expected: submission.metadata.priority equals `4`
   - Expected: submission.metadata.deadline equals `900u64`
   - Expected: submission.metadata.dependency_value equals `12u64`
   - Expected: submission.metadata.flags equals `3u64`
   - Expected: submission.metadata.trace_id equals `88u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("validates registered payload ownership and carries the lease to the provider")
val value = ring(1)
val lease = RingPayloadLease(
    ownership: RingPayloadOwnership.RegisteredLease, owner_id: 7u64,
    handle: 55u64, generation: RingGeneration(value: 3u64), byte_length: 4096u64)
val metadata = RingOperationMetadata(
    resource_handle: 66u64, task_key: 77u64, priority: 4,
    deadline: 900u64, dependency_value: 12u64, flags: 3u64,
    payload_lease: lease, trace_id: 88u64)
val held = match value.reserve_with_metadata(7u64, metadata):
    case Ok(item): item
    case Err(_): fail("registered payload reservation failed")
match value.commit(7u64, held, 9):
    case Ok(_): ()
    case Err(_): fail("registered payload commit failed")
val submission = match value.provider_take(1):
    case Ok(Some(item)): item
    case Ok(nil): fail("registered payload submission missing")
    case Err(_): fail("registered payload take failed")
expect(submission.payload_lease.handle).to_equal(55u64)
expect(submission.payload_lease.generation.value).to_equal(3u64)
expect(submission.payload_lease.byte_length).to_equal(4096u64)
expect(submission.metadata.resource_handle).to_equal(66u64)
expect(submission.metadata.priority).to_equal(4)
expect(submission.metadata.deadline).to_equal(900u64)
expect(submission.metadata.dependency_value).to_equal(12u64)
expect(submission.metadata.flags).to_equal(3u64)
expect(submission.metadata.trace_id).to_equal(88u64)
var invalid = lease
invalid.owner_id = 8u64
match value.reserve_with_payload(7u64, 88u64, invalid):
    case Err(error): expect(error).to_equal(SimpleRingError.InvalidPayloadLease)
    case Ok(_): fail("foreign payload lease was admitted")
```

</details>

#### reset invalidates outstanding tokens and restores all capacity

- reset invalidates outstanding tokens and restores all capacity
   - Expected: receipt.ring_id equals `99u64`
   - Expected: receipt.invalidated equals `1u64`
   - Expected: value.occupancy() equals `0u64`
   - Expected: value.telemetry().stale_rejects equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reset invalidates outstanding tokens and restores all capacity")
val value = ring(2)
val held = reservation(value, 10u64)
match value.commit(7u64, held, 1):
    case Ok(_): ()
    case Err(_): fail("commit failed")
val receipt = match value.reset(7u64):
    case Ok(item): item
    case Err(_): fail("reset failed")
expect(receipt.ring_id).to_equal(99u64)
expect(receipt.invalidated).to_equal(1u64)
expect(value.occupancy()).to_equal(0u64)
val after_reset = reservation(value, 30u64)
expect(after_reset.token.generation.value).to_be_greater_than(held.token.generation.value)
match value.complete_cancelled(held.token, "stale provider"):
    case Err(error): expect(error).to_equal(SimpleRingError.StaleToken)
    case Ok(_): fail("reset token completed")
expect(value.telemetry().stale_rejects).to_equal(1u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/async_ring/simple_ring_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleRing fixed-capacity lifecycle.
- SimpleRing fixed-capacity lifecycle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `f0c7a91dc0402224194eb1c6c82d92ee4a9cc807767eb6b439231304f3452dc4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f0c7a91dc0402224194eb1c6c82d92ee4a9cc807767eb6b439231304f3452dc4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f0c7a91dc0402224194eb1c6c82d92ee4a9cc807767eb6b439231304f3452dc4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_async_mut/async_ring/simple_ring_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/async_ring/simple_ring_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/async_ring/simple_ring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/async_ring/simple_ring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/async_ring/simple_ring_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/async_ring/simple_ring_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reserves and commits batches with all-or-nothing validation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/async_ring/simple_ring_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid construction and wrong mutable owner' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/async_ring/simple_ring_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is bounded and advances free indices through release without scanning' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
