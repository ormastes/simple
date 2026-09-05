# Mission Adapter Specification

> Tests covering mission SimpleRing adapter admission evidence, mission SimpleRing adapter owner and lifecycle, mission SimpleRing adapter forwarding.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mission Adapter Specification

## Scenarios

### mission SimpleRing adapter admission evidence

#### constructs in Configuring and rejects invalid identities

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- constructs in Configuring and rejects invalid identities
   - Expected: adapter(2).lifecycle() equals `MissionRingLifecycle.Configuring`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("constructs in Configuring and rejects invalid identities")
match MissionSimpleRingAdapter<i64, i64>.create(0u64, 1u64, 1):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.InvalidOwner)
    case Ok(_): fail("zero owner accepted")
match MissionSimpleRingAdapter<i64, i64>.create(OWNER, 0u64, 1):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.InvalidRingId)
    case Ok(_): fail("zero ring accepted")
match MissionSimpleRingAdapter<i64, i64>.create(OWNER, 1u64, 0):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.InvalidCapacity)
    case Ok(_): fail("zero capacity accepted")
expect(adapter(2).lifecycle()).to_equal(MissionRingLifecycle.Configuring)
```

</details>

#### admits mission_alloc only with sealed bounded arena evidence

- admits mission_alloc only with sealed bounded arena evidence
   - Expected: value.lifecycle() equals `MissionRingLifecycle.Ready`
   - Expected: receipt.profile_id equals `mission_alloc`
   - Expected: receipt.capacity equals `2u64`
   - Expected: receipt.evidence_level equals `MissionRingEvidenceLevel.HostedPreallocatedV1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("admits mission_alloc only with sealed bounded arena evidence")
val value = adapter(2)
val receipt = match value.configure(
    OWNER, async_profile_mission_alloc_v1(), alloc_evidence(2u64)):
    case Ok(item): item
    case Err(_): fail("valid mission_alloc rejected")
expect(value.lifecycle()).to_equal(MissionRingLifecycle.Ready)
expect(receipt.profile_id).to_equal("mission_alloc")
expect(receipt.capacity).to_equal(2u64)
expect(receipt.evidence_level).to_equal(MissionRingEvidenceLevel.HostedPreallocatedV1)
expect(receipt.link_time_static_proven).to_be(false)
expect(receipt.allocation_free_proven).to_be(false)
expect(receipt.profile_fingerprint.len()).to_be_greater_than(0)
```

</details>

#### admits mission_pool only with fixed pool and compiler frame bounds

- admits mission_pool only with fixed pool and compiler frame bounds
   - Expected: receipt.profile_id equals `mission_pool`
   - Expected: value.profile_fingerprint() equals `receipt.profile_fingerprint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("admits mission_pool only with fixed pool and compiler frame bounds")
val value = adapter(3)
val receipt = match value.configure(
    OWNER, async_profile_mission_pool_v1(), pool_evidence(3u64)):
    case Ok(item): item
    case Err(_): fail("valid mission_pool rejected")
expect(receipt.profile_id).to_equal("mission_pool")
expect(value.profile_fingerprint()).to_equal(receipt.profile_fingerprint)
```

</details>

#### rejects non-mission, indirect, fallback, and undersized evidence

- rejects non-mission, indirect, fallback, and undersized evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects non-mission, indirect, fallback, and undersized evidence")
val ordinary = adapter(2)
match ordinary.configure(OWNER, async_profile_common_v1(), alloc_evidence(2u64)):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.NonMissionProfile)
    case Ok(_): fail("ordinary profile admitted")
var indirect = alloc_evidence(2u64)
indirect.provider_mapping = RingMappingGrade.Translated
match adapter(2).configure(OWNER, async_profile_mission_alloc_v1(), indirect):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.DirectMappingRequired)
    case Ok(_): fail("translated provider admitted")
var fallback = alloc_evidence(2u64)
fallback.fallback_selected = true
match adapter(2).configure(OWNER, async_profile_mission_alloc_v1(), fallback):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.FallbackForbidden)
    case Ok(_): fail("fallback admitted")
var arena = alloc_evidence(1u64)
arena.sealed_arena = true
match adapter(2).configure(OWNER, async_profile_mission_alloc_v1(), arena):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.ArenaCapacityInsufficient)
    case Ok(_): fail("undersized arena admitted")
match adapter(2).configure(OWNER, async_profile_mission_pool_v1(), pool_evidence(1u64)):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.StaticPoolCapacityInsufficient)
    case Ok(_): fail("undersized pool admitted")
```

</details>

#### rejects missing, excessive, and profile-exceeding bounds

- rejects missing, excessive, and profile-exceeding bounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects missing, excessive, and profile-exceeding bounds")
var missing = pool_evidence(2u64)
missing.compiler_known_frame_bytes = 0u64
match adapter(2).configure(OWNER, async_profile_mission_pool_v1(), missing):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.FrameBoundRequired)
    case Ok(_): fail("missing frame bound admitted")
var excessive = pool_evidence(2u64)
excessive.compiler_known_frame_bytes = 513u64
match adapter(2).configure(OWNER, async_profile_mission_pool_v1(), excessive):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.FrameBoundExceeded)
    case Ok(_): fail("excessive frame admitted")
var bounded = async_profile_mission_alloc_v1()
bounded.bounds.max_tasks = 1u64
bounded.bounds.max_operations = 1u64
bounded.bounds.max_buffers = 1u64
bounded.bounds.max_traces = 1u64
bounded.bounds.max_deadlines = 1u64
match adapter(2).configure(OWNER, bounded, alloc_evidence(2u64)):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.CapacityExceedsProfile)
    case Ok(_): fail("capacity above profile admitted")
```

</details>

#### rejects every undersized mission resource class before Ready

- rejects every undersized mission resource class before Ready


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects every undersized mission resource class before Ready")
var evidence = pool_evidence(2u64)
evidence.task_slots = 1023u64
match adapter(2).configure(OWNER, async_profile_mission_pool_v1(), evidence):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.TaskCapacityInsufficient)
    case Ok(_): fail("undersized task pool admitted")
evidence = pool_evidence(2u64)
evidence.operation_slots = 4095u64
match adapter(2).configure(OWNER, async_profile_mission_pool_v1(), evidence):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.OperationCapacityInsufficient)
    case Ok(_): fail("undersized operation pool admitted")
evidence = pool_evidence(2u64)
evidence.buffer_slots = 4095u64
match adapter(2).configure(OWNER, async_profile_mission_pool_v1(), evidence):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.BufferCapacityInsufficient)
    case Ok(_): fail("undersized buffer pool admitted")
evidence = pool_evidence(2u64)
evidence.trace_slots = 1023u64
match adapter(2).configure(OWNER, async_profile_mission_pool_v1(), evidence):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.TraceCapacityInsufficient)
    case Ok(_): fail("undersized trace pool admitted")
evidence = pool_evidence(2u64)
evidence.deadline_slots = 1023u64
match adapter(2).configure(OWNER, async_profile_mission_pool_v1(), evidence):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.DeadlineCapacityInsufficient)
    case Ok(_): fail("undersized deadline pool admitted")
evidence = pool_evidence(2u64)
evidence.timer_slots = 1023u64
match adapter(2).configure(OWNER, async_profile_mission_pool_v1(), evidence):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.TimerCapacityInsufficient)
    case Ok(_): fail("undersized timer pool admitted")
evidence = pool_evidence(2u64)
evidence.join_cancel_slots = 1023u64
match adapter(2).configure(OWNER, async_profile_mission_pool_v1(), evidence):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.JoinCancelCapacityInsufficient)
    case Ok(_): fail("undersized join/cancellation pool admitted")
```

</details>

### mission SimpleRing adapter owner and lifecycle

#### rejects every operation before Ready and rejects foreign owners

- rejects every operation before Ready and rejects foreign owners


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects every operation before Ready and rejects foreign owners")
val value = adapter(1)
match value.reserve(OWNER, 10u64):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.NotReady)
    case Ok(_): fail("pre-Ready operation admitted")
match value.configure(8u64, async_profile_mission_alloc_v1(), alloc_evidence(1u64)):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.WrongOwner)
    case Ok(_): fail("foreign owner configured")
configure_alloc(value)
match value.reserve(8u64, 10u64):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.WrongOwner)
    case Ok(_): fail("foreign owner reserved")
match value.configure(OWNER, async_profile_mission_alloc_v1(), alloc_evidence(1u64)):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.NotConfiguring)
    case Ok(_): fail("Ready adapter reconfigured")
```

</details>

#### requires a drained ring before terminal quiescence

- requires a drained ring before terminal quiescence
   - Expected: value.lifecycle() equals `MissionRingLifecycle.Quiesced`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires a drained ring before terminal quiescence")
val value = adapter(1)
configure_alloc(value)
val held = reserve(value, 10u64)
match value.quiesce(OWNER):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.RingNotDrained)
    case Ok(_): fail("occupied ring quiesced")
match value.release(OWNER, held):
    case Ok(_): ()
    case Err(_): fail("release failed")
match value.quiesce(OWNER):
    case Ok(_): ()
    case Err(_): fail("drained ring did not quiesce")
expect(value.lifecycle()).to_equal(MissionRingLifecycle.Quiesced)
match value.reserve(OWNER, 20u64):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.NotReady)
    case Ok(_): fail("post-quiesce operation admitted")
match value.quiesce(OWNER):
    case Err(error): expect(error).to_equal(MissionRingAdapterError.AlreadyQuiesced)
    case Ok(_): fail("second quiesce accepted")
```

</details>

### mission SimpleRing adapter forwarding

#### returns canonical Pending and wakes exactly the submitting task

- returns canonical Pending and wakes exactly the submitting task
   - Expected: wake.wake_key equals `1234u64`
   - Expected: wake.token equals `item.token`
   - Expected: wake.kind equals `RingTerminalKind.Success`
   - Expected: item.task_key equals `1234u64`
   - Expected: item.kind equals `RingTerminalKind.Success`
   - Expected: result equals `42`
   - Expected: value.occupancy() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns canonical Pending and wakes exactly the submitting task")
val value = adapter(2)
configure_alloc(value)
val held = reserve(value, 1234u64)
val pending = match value.commit(OWNER, held, 41):
    case Ok(item): item
    case Err(_): fail("commit failed")
match pending:
    case TaskPollResult.Pending(token): expect(token.ring_id).to_equal(99u64)
    case TaskPollResult.Ready(_): fail("latency operation reported Ready")
val submission = match value.provider_take(OWNER):
    case Ok(item): item
    case Err(_): fail("provider take failed")
if val item = submission:
    val wake = match value.complete_success(OWNER, item, 42):
        case Ok(receipt): receipt
        case Err(_): fail("completion failed")
    expect(wake.wake_key).to_equal(1234u64)
    expect(wake.token).to_equal(item.token)
    expect(wake.kind).to_equal(RingTerminalKind.Success)
else:
    fail("submission missing")
val completion = match value.take_completion(OWNER):
    case Ok(item): item
    case Err(_): fail("completion take failed")
if val item = completion:
    expect(item.task_key).to_equal(1234u64)
    expect(item.kind).to_equal(RingTerminalKind.Success)
    if val result = item.value:
        expect(result).to_equal(42)
    else:
        fail("completion value missing")
else:
    fail("completion missing")
expect(value.occupancy()).to_equal(0u64)
```

</details>

#### forwards bounded batch, failure, cancellation, and reset semantics

- forwards bounded batch, failure, cancellation, and reset semantics
   - Expected: error equals `SimpleRingError.Full`
   - Expected: reset.invalidated equals `2u64`
   - Expected: value.occupancy() equals `0u64`
   - Expected: value.telemetry().completions equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("forwards bounded batch, failure, cancellation, and reset semantics")
val value = adapter(2)
configure_alloc(value)
match value.commit_batch(OWNER, [10u64, 20u64], [1, 2]):
    case Ok(receipt): expect(receipt.committed).to_equal(2u64)
    case Err(_): fail("bounded batch failed")
match value.commit_batch(OWNER, [30u64], [3]):
    case Err(MissionRingAdapterError.RingRejected(error)):
        expect(error).to_equal(SimpleRingError.Full)
    case _: fail("full ring batch did not fail closed")
val first = match value.provider_take(OWNER):
    case Ok(item): item
    case Err(_): fail("first take failed")
if val submission = first:
    match value.complete_failure(OWNER, submission, "device-fault"):
        case Ok(wake): expect(wake.kind).to_equal(RingTerminalKind.Failure)
        case Err(_): fail("failure publish failed")
else:
    fail("first submission missing")
val second = match value.provider_take(OWNER):
    case Ok(item): item
    case Err(_): fail("second take failed")
if val submission = second:
    match value.cancel(OWNER, submission.token):
        case Ok(RingCancelOutcome.ProviderCancelRequested(_)): ()
        case _: fail("provider cancellation not requested")
    match value.complete_cancelled(OWNER, submission, "cancelled"):
        case Ok(wake): expect(wake.kind).to_equal(RingTerminalKind.Cancelled)
        case Err(_): fail("cancel completion failed")
else:
    fail("second submission missing")
val reset = match value.reset(OWNER):
    case Ok(receipt): receipt
    case Err(_): fail("reset failed")
expect(reset.invalidated).to_equal(2u64)
expect(value.occupancy()).to_equal(0u64)
expect(value.telemetry().completions).to_equal(2u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/async_ring/mission_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering mission SimpleRing adapter admission evidence, mission SimpleRing adapter owner and lifecycle, mission SimpleRing adapter forwarding.
- mission SimpleRing adapter admission evidence
- mission SimpleRing adapter owner and lifecycle
- mission SimpleRing adapter forwarding

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

- Canonical SPipe generation for source `fbea05d3f9bd06020e3ef81054f8af8e4de1cfde756a2d6db09290738e6f9922`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fbea05d3f9bd06020e3ef81054f8af8e4de1cfde756a2d6db09290738e6f9922`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fbea05d3f9bd06020e3ef81054f8af8e4de1cfde756a2d6db09290738e6f9922`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/nogc_async_mut/async_ring/mission_adapter_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/async_ring/mission_adapter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/async_ring/mission_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/async_ring/mission_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/async_ring/mission_adapter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_async_mut/async_ring/mission_adapter_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'constructs in Configuring and rejects invalid identities' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/async_ring/mission_adapter_spec.spl:217:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires a drained ring before terminal quiescence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/async_ring/mission_adapter_spec.spl:241:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns canonical Pending and wakes exactly the submitting task' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
