# simple_ring_async_base_spec

> Operator scenarios for the SimpleRing V1 async foundation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_ring_async_base_spec

Operator scenarios for the SimpleRing V1 async foundation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/03_system/runtime/simple_ring_async_base_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Operator scenarios for the SimpleRing V1 async foundation.

These scenarios exercise the real bounded ring, profile contract, and software
provider. They prove hosted V1 lifecycle behavior only; they do not claim a
native OS provider, compiler-generated async lowering, or a migrated executor.

## Scenarios

### SimpleRing and async profile V1 foundation

#### admits a compatible profile with a stable provider fingerprint

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Profile admission (expected show, folded, detail, or skip)


- Configure the async execution profile
   - Expected: admission.mapping equals `RingMappingGrade.Software`
   - Expected: admission.profile_id equals `server`
   - Expected: admission.fallback_fact equals `software-grade-selected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SRA-010, REQ-SRA-012, REQ-SRA-015, REQ-SSPEC-SYSTEM
step("Configure the async execution profile")
val fixture = setup_simple_ring_profile_fixture(async_profile_server_v1())
val provider = fixture.provider
match async_profile_validate_v1(fixture.profile):
    case Ok(_): ()
    case Err(_): fail("server profile validation failed")
val admission = provider.admit(fixture.profile)
match admission.status:
    case SoftwareProviderAdmissionStatus.Admitted:
        expect(admission.mapping).to_equal(RingMappingGrade.Software)
        expect(admission.profile_id).to_equal("server")
        expect(admission.profile_fingerprint).to_equal(
            async_profile_fingerprint_v1(fixture.profile))
        expect(admission.fallback_fact).to_equal("software-grade-selected")
    case SoftwareProviderAdmissionStatus.Rejected:
        fail("compatible server profile was rejected")
check_simple_ring_invariants(fixture)
```

</details>

#### reserves and commits a bounded all-or-nothing batch

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Bounded submission (expected show, folded, detail, or skip)


- Configure the async execution profile
- Reserve and commit bounded ring work
   - Expected: work_ring.occupancy() equals `2u64`
   - Expected: work_ring.high_water() equals `2u64`
   - Expected: work_ring.occupancy() equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SRA-001, REQ-SRA-002, REQ-SRA-003, REQ-SRA-004
val fixture = setup_simple_ring_profile_fixture(async_profile_common_v1())
val work_ring = fixture.ring
val provider = fixture.provider

step("Configure the async execution profile")
match provider.admit(fixture.profile).status:
    case SoftwareProviderAdmissionStatus.Admitted: ()
    case SoftwareProviderAdmissionStatus.Rejected: fail("common profile rejected")

step("Reserve and commit bounded ring work")
match work_ring.commit_batch(
    fixture.owner_id, [7001u64, 7002u64], [11, 22],
    RingBatchPolicy.AllOrNothing):
    case Ok(receipt): expect(receipt.committed).to_equal(2u64)
    case Err(_): fail("bounded batch commit failed")
expect(work_ring.occupancy()).to_equal(2u64)
expect(work_ring.high_water()).to_equal(2u64)
match work_ring.commit_batch(
    fixture.owner_id, [7003u64, 7004u64, 7005u64], [33, 44, 55],
    RingBatchPolicy.AllOrNothing):
    case Err(error): expect(error).to_equal(SimpleRingError.Full)
    case Ok(_): fail("over-capacity batch partially committed")
expect(work_ring.occupancy()).to_equal(2u64)
check_simple_ring_invariants(fixture)
```

</details>

#### publishes one completion and wakes only its task key

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Completion and wakeup (expected show, folded, detail, or skip)


- Configure the async execution profile
- Reserve and commit bounded ring work
   - Expected: submission.payload_lease.handle equals `4401u64`
   - Expected: submission.payload_lease.byte_length equals `8192u64`
- Complete work and wake the exact task
   - Expected: wake.wake_key equals `8001u64`
   - Expected: wake.kind equals `RingTerminalKind.Success`
   - Expected: wake.provider_id equals `5101u64`
   - Expected: completion.task_key equals `8001u64`
   - Expected: completion.kind equals `RingTerminalKind.Success`
   - Expected: value equals `done`
   - Expected: provider.counters().wakes equals `1u64`
   - Expected: work_ring.occupancy() equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SRA-006, REQ-SRA-007, REQ-SRA-010, REQ-SRA-011
val fixture = setup_simple_ring_profile_fixture(async_profile_common_v1())
val work_ring = fixture.ring
val provider = fixture.provider

step("Configure the async execution profile")
match provider.admit(fixture.profile).status:
    case SoftwareProviderAdmissionStatus.Admitted: ()
    case SoftwareProviderAdmissionStatus.Rejected: fail("common profile rejected")

step("Reserve and commit bounded ring work")
val payload_lease = RingPayloadLease(
    ownership: RingPayloadOwnership.RegisteredLease,
    owner_id: fixture.owner_id, handle: 4401u64,
    generation: RingGeneration(value: 2u64), byte_length: 8192u64)
val reservation = match work_ring.reserve_with_payload(
    fixture.owner_id, 8001u64, payload_lease):
    case Ok(value): value
    case Err(_): fail("ring reservation failed")
match work_ring.commit(fixture.owner_id, reservation, 42):
    case Ok(_): ()
    case Err(_): fail("ring commit failed")
val submission = match provider.take_one(work_ring):
    case Ok(Some(value)): value
    case Ok(nil): fail("provider observed no committed work")
    case Err(_): fail("provider take failed")
expect(submission.payload_lease.handle).to_equal(4401u64)
expect(submission.payload_lease.byte_length).to_equal(8192u64)

step("Complete work and wake the exact task")
match provider.complete_success(work_ring, submission, "done"):
    case Ok(wake):
        expect(wake.wake_key).to_equal(8001u64)
        expect(wake.kind).to_equal(RingTerminalKind.Success)
        expect(wake.provider_id).to_equal(5101u64)
    case Err(_): fail("provider completion failed")
val completion = match work_ring.take_completion(fixture.owner_id):
    case Ok(Some(value)): value
    case Ok(nil): fail("terminal completion was not queued")
    case Err(_): fail("completion take failed")
expect(completion.task_key).to_equal(8001u64)
expect(completion.kind).to_equal(RingTerminalKind.Success)
if val value = completion.value:
    expect(value).to_equal("done")
else:
    fail("successful completion carried no value")
expect(provider.counters().wakes).to_equal(1u64)
expect(work_ring.occupancy()).to_equal(0u64)
check_simple_ring_invariants(fixture)
```

</details>

#### rejects capacity overflow, duplicate completion, and stale reset tokens

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Rejection behavior (expected show, folded, detail, or skip)


- Reserve and commit bounded ring work
- Complete work and wake the exact task
- Reject stale, duplicate, and over-capacity activity
   - Expected: work_ring.telemetry().duplicate_rejects equals `1u64`
   - Expected: work_ring.telemetry().stale_rejects equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SRA-002, REQ-SRA-004, REQ-SRA-005
val fixture = setup_simple_ring_profile_fixture(async_profile_common_v1())
val work_ring = fixture.ring
val provider = fixture.provider

step("Reserve and commit bounded ring work")
val held = match work_ring.reserve(fixture.owner_id, 9001u64):
    case Ok(value): value
    case Err(_): fail("first reservation failed")
match work_ring.commit(fixture.owner_id, held, 99):
    case Ok(_): ()
    case Err(_): fail("first commit failed")
val submission = match provider.take_one(work_ring):
    case Ok(Some(value)): value
    case Ok(nil): fail("provider submission missing")
    case Err(_): fail("provider take failed")

step("Complete work and wake the exact task")
match provider.complete_success(work_ring, submission, "first"):
    case Ok(wake): expect(wake.wake_key).to_equal(9001u64)
    case Err(_): fail("first completion failed")

step("Reject stale, duplicate, and over-capacity activity")
match work_ring.complete_success(submission.token, "duplicate"):
    case Err(error): expect(error).to_equal(SimpleRingError.TerminalAlreadyPublished)
    case Ok(_): fail("duplicate terminal completion was accepted")
match work_ring.take_completion(fixture.owner_id):
    case Ok(Some(value)): expect(value.task_key).to_equal(9001u64)
    case Ok(nil): fail("first completion missing")
    case Err(_): fail("first completion take failed")
val pending = match work_ring.reserve(fixture.owner_id, 9002u64):
    case Ok(value): value
    case Err(_): fail("reset reservation failed")
match work_ring.reset(fixture.owner_id):
    case Ok(receipt): expect(receipt.invalidated).to_equal(1u64)
    case Err(_): fail("ring reset failed")
match work_ring.complete_cancelled(pending.token, "late completion"):
    case Err(error): expect(error).to_equal(SimpleRingError.StaleToken)
    case Ok(_): fail("pre-reset token completed after reset")
expect(work_ring.telemetry().duplicate_rejects).to_equal(1u64)
expect(work_ring.telemetry().stale_rejects).to_equal(1u64)
check_simple_ring_invariants(fixture)
```

</details>

#### keeps mission allocation and pool profiles bounded and deterministic

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Mission policy (expected show, folded, detail, or skip)


- Configure the async execution profile
- Prove mission bounds and deterministic policy
   - Expected: mission_alloc.preset equals `AsyncProfilePreset.MissionAlloc`
   - Expected: mission_alloc.memory equals `AsyncMemory.Arena`
   - Expected: mission_alloc.scheduler equals `AsyncScheduler.FixedPriority`
   - Expected: mission_alloc.assurance equals `AsyncAssurance.Mission`
   - Expected: mission_pool.preset equals `AsyncProfilePreset.MissionPool`
   - Expected: mission_pool.memory equals `AsyncMemory.Pool`
   - Expected: mission_pool.scheduler equals `AsyncScheduler.Cooperative`
   - Expected: mission_pool.mapping equals `AsyncRingMapping.DirectRequired`
   - Expected: provider.mapping_grade() equals `RingMappingGrade.Software`
   - Expected: mission_receipt.capacity equals `4u64`
   - Expected: trace_ring.telemetry().high_water equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 76 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SRA-012, REQ-SRA-013, REQ-SRA-014, REQ-SRA-015
step("Configure the async execution profile")
val mission_alloc = async_profile_mission_alloc_v1()
val mission_pool = async_profile_mission_pool_v1()
match async_profile_validate_v1(mission_alloc):
    case Ok(_): ()
    case Err(_): fail("mission_alloc profile validation failed")
match async_profile_validate_v1(mission_pool):
    case Ok(_): ()
    case Err(_): fail("mission_pool profile validation failed")

step("Prove mission bounds and deterministic policy")
expect(mission_alloc.preset).to_equal(AsyncProfilePreset.MissionAlloc)
expect(mission_alloc.memory).to_equal(AsyncMemory.Arena)
expect(mission_alloc.scheduler).to_equal(AsyncScheduler.FixedPriority)
expect(mission_alloc.assurance).to_equal(AsyncAssurance.Mission)
expect(mission_alloc.deterministic).to_be(true)
expect(mission_alloc.blocking_allowed).to_be(false)
expect(mission_alloc.allocation_after_admission_allowed).to_be(false)
expect(mission_pool.preset).to_equal(AsyncProfilePreset.MissionPool)
expect(mission_pool.memory).to_equal(AsyncMemory.Pool)
expect(mission_pool.scheduler).to_equal(AsyncScheduler.Cooperative)
expect(mission_pool.mapping).to_equal(AsyncRingMapping.DirectRequired)
expect(mission_pool.work_stealing_allowed).to_be(false)
expect(mission_pool.detached_tasks_allowed).to_be(false)
expect(mission_pool.compiler_known_frame_bounds_required).to_be(true)
expect(mission_pool.bounds.max_tasks).to_be_greater_than(0u64)
expect(async_profile_fingerprint_v1(mission_pool)).to_equal(
    async_profile_fingerprint_v1(async_profile_mission_pool_v1()))

val fixture = setup_simple_ring_profile_fixture(mission_pool)
val provider = fixture.provider
match provider.admit(mission_pool).status:
    case SoftwareProviderAdmissionStatus.Rejected: ()
    case SoftwareProviderAdmissionStatus.Admitted:
        fail("software provider admitted a direct-required mission profile")
expect(provider.mapping_grade()).to_equal(RingMappingGrade.Software)
val mission_adapter = match MissionSimpleRingAdapter<i64, text>.create(
    92u64, 4201u64, 4):
    case Ok(value): value
    case Err(_): fail("mission adapter construction failed")
val mission_evidence = MissionRingEvidence(
    provider_mapping: RingMappingGrade.Direct, fallback_selected: false,
    sealed_arena: false, arena_capacity: 0u64,
    static_pool_ready: true, static_pool_capacity: 4u64,
    task_slots: 1024u64, operation_slots: 4096u64,
    buffer_slots: 4096u64, trace_slots: 1024u64,
    deadline_slots: 1024u64, timer_slots: 1024u64,
    join_cancel_slots: 1024u64,
    maximum_frame_bytes: 512u64, compiler_known_frame_bytes: 128u64)
val mission_receipt = match mission_adapter.configure(
    92u64, mission_pool, mission_evidence):
    case Ok(value): value
    case Err(_): fail("bounded mission_pool admission failed")
expect(mission_receipt.evidence_level).to_equal(
    MissionRingEvidenceLevel.HostedPreallocatedV1)
expect(mission_receipt.capacity).to_equal(4u64)
expect(mission_receipt.link_time_static_proven).to_be(false)
expect(mission_receipt.allocation_free_proven).to_be(false)

val trace_ring = match AsyncTraceRing.create(
    92u64, 4, AsyncTraceFullPolicy.RejectNewest):
    case Ok(value): value
    case Err(_): fail("bounded trace ring construction failed")
match trace_ring.seal(92u64):
    case Ok(receipt): expect(receipt.capacity).to_equal(4u64)
    case Err(_): fail("bounded trace ring seal failed")
val ready_event = AsyncTraceEvent(
    kind: AsyncTraceEventKind.TaskReady, task_id: 9901u64,
    parent_task_id: 0u64, ring_id: 4201u64, operation_token: nil,
    provider_id: 0u64, trace_id: 8801u64, sequence: 1u64)
match trace_ring.append(92u64, ready_event):
    case Ok(outcome): expect(outcome).to_equal(AsyncTraceAppendOutcome.Appended)
    case Err(_): fail("bounded trace append failed")
expect(trace_ring.telemetry().high_water).to_equal(1u64)
check_simple_ring_invariants(fixture)
```

</details>

#### keeps wake selection bounded, nonblocking, deterministic, and generation safe

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Nonfunctional acceptance mechanisms (expected show, folded, detail, or skip)


- Verify bounded nonfunctional ring behavior
   - Expected: token.ring_id equals `reservation.token.ring_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: NFR-SRA-001, NFR-SRA-002, NFR-SRA-003, NFR-SRA-004, NFR-SRA-005
step("Verify bounded nonfunctional ring behavior")
var ready_set = match MissionReadySet64.create(93u64, 8u64):
    case Ok(value): value
    case Err(_): fail("mission ready set construction failed")
match ready_set.seal(93u64):
    case Ok(receipt): expect(receipt.capacity).to_equal(8u64)
    case Err(_): fail("mission ready set seal failed")
val ready_token = match ready_set.admit(93u64, 5u64):
    case Ok(value): value
    case Err(_): fail("bounded task slot admission failed")
match ready_set.post_ready(93u64, ready_token):
    case Ok(_): ()
    case Err(_): fail("exact task wake post failed")
expect(ready_set.is_ready(5u64)).to_be(true)
match ready_set.claim_ready(93u64, ready_token):
    case Ok(_): ()
    case Err(_): fail("exact task wake claim failed")
expect(ready_set.is_ready(5u64)).to_be(false)

val fixture = setup_simple_ring_profile_fixture(async_profile_common_v1())
val reservation = match fixture.ring.reserve(fixture.owner_id, 9301u64):
    case Ok(value): value
    case Err(_): fail("compatibility wait reservation failed")
val compat = match poll_future_compat(Future<i64>.pending(), reservation.token):
    case Ok(value): value
    case Err(_): fail("nonblocking compatibility poll failed")
match compat.poll_result:
    case TaskPollResult.Pending(token):
        expect(token.ring_id).to_equal(reservation.token.ring_id)
        expect(token.generation.value).to_equal(
            reservation.token.generation.value)
    case TaskPollResult.Ready(_): fail("pending compatibility future became ready")
expect(compat.blocking_used).to_be(false)
expect(compat.scheduler_created).to_be(false)
```

</details>

#### reports portable mapping, compatibility, and telemetry facts explicitly

**Manual warnings:**
- invalid manual visibility metadata: # @manual_section: Portable profile and compatibility policy (expected show, folded, detail, or skip)


- Verify portable provider and compatibility facts
   - Expected: admission.mapping equals `RingMappingGrade.Software`
   - Expected: admission.fallback_fact equals `software-grade-selected`
   - Expected: telemetry.high_water equals `0u64`
   - Expected: telemetry.full_events equals `0u64`
   - Expected: telemetry.batches equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: NFR-SRA-010, NFR-SRA-011, REQ-SRA-016, REQ-SRA-017
step("Verify portable provider and compatibility facts")
val fixture = setup_simple_ring_profile_fixture(async_profile_server_v1())
val admission = fixture.provider.admit_for_depth(fixture.profile, 4)
match admission.status:
    case SoftwareProviderAdmissionStatus.Admitted:
        expect(admission.mapping).to_equal(RingMappingGrade.Software)
        expect(admission.bounded).to_be(true)
        expect(admission.fallback_fact).to_equal("software-grade-selected")
        expect(admission.fallback_reason).to_equal(
            "software ring provider selected")
    case SoftwareProviderAdmissionStatus.Rejected:
        fail("bounded server provider was rejected")
val telemetry = fixture.ring.telemetry()
expect(telemetry.high_water).to_equal(0u64)
expect(telemetry.full_events).to_equal(0u64)
expect(telemetry.batches).to_equal(0u64)
expect(fixture.profile.blocking_allowed).to_be(false)
expect(fixture.profile.single_owner_mutable_queues_required).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-SRA-010`
- `REQ-SRA-012`
- `REQ-SRA-015`
- `REQ-SRA-001`
- `REQ-SRA-002`
- `REQ-SRA-003`
- `REQ-SRA-004`
- `REQ-SRA-006`
- `REQ-SRA-007`
- `REQ-SRA-011`
- `REQ-SRA-005`
- `REQ-SRA-013`
- `REQ-SRA-014`
- `REQ-SRA-016`
- `REQ-SRA-017`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7d305fc9657e99816d8434feda976a651c98db9f1047a2406e9b77b50469dfa5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7d305fc9657e99816d8434feda976a651c98db9f1047a2406e9b77b50469dfa5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7d305fc9657e99816d8434feda976a651c98db9f1047a2406e9b77b50469dfa5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/runtime/simple_ring_async_base_spec.spl
mirror: doc/06_spec/03_system/runtime/simple_ring_async_base_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/runtime/simple_ring_async_base_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/runtime/simple_ring_async_base_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/runtime/simple_ring_async_base_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits a compatible profile with a stable provider fingerprint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/runtime/simple_ring_async_base_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reserves and commits a bounded all-or-nothing batch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/runtime/simple_ring_async_base_spec.spl:125:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'publishes one completion and wakes only its task key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
