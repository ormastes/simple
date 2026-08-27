# Async Profile V1 Specification

> Tests covering AsyncProfile v1 presets, AsyncProfile v1 fail-closed validation, AsyncProfile v1 canonical fingerprint, AsyncProfile v1 exhaustive structural branches, AsyncProfile v1 exhaustive mission branches, AsyncProfile v1 exhaustive fingerprint sensitivity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async Profile V1 Specification

## Scenarios

### AsyncProfile v1 presets

#### admits every canonical preset

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(async_profile_validate_v1(async_profile_common_v1())).to_equal(Ok(()))
expect(async_profile_validate_v1(async_profile_script_v1())).to_equal(Ok(()))
expect(async_profile_validate_v1(async_profile_server_v1())).to_equal(Ok(()))
expect(async_profile_validate_v1(async_profile_mission_alloc_v1())).to_equal(Ok(()))
expect(async_profile_validate_v1(async_profile_mission_pool_v1())).to_equal(Ok(()))
```

</details>

#### selects every named preset through the canonical selector

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(async_profile_preset_v1(AsyncProfilePreset.Common).profile_id).to_equal("common")
expect(async_profile_preset_v1(AsyncProfilePreset.Script).profile_id).to_equal("script")
expect(async_profile_preset_v1(AsyncProfilePreset.Server).profile_id).to_equal("server")
expect(async_profile_preset_v1(AsyncProfilePreset.MissionAlloc).profile_id).to_equal("mission_alloc")
expect(async_profile_preset_v1(AsyncProfilePreset.MissionPool).profile_id).to_equal("mission_pool")
```

</details>

### AsyncProfile v1 fail-closed validation

#### rejects malformed bounds and incompatible surface policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var profile = async_profile_common_v1()
profile.bounds.max_tasks = 0u64
val bounds = async_profile_validate_v1(profile)
expect(bounds).to_equal(Err(AsyncProfileError.InvalidBounds))
profile = async_profile_common_v1()
profile.policy = AsyncPolicy.Forbidden
val policy = async_profile_validate_v1(profile)
expect(policy).to_equal(Err(AsyncProfileError.InvalidSurfacePolicy))
```

</details>

#### rejects direct mapping fallback and undeclared work stealing

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var direct = async_profile_mission_alloc_v1()
direct.fallback_allowed = true
expect(async_profile_validate_v1(direct)).to_equal(Err(AsyncProfileError.InvalidMappingFallback))
var stealing = async_profile_common_v1()
stealing.scheduler = AsyncScheduler.ComputeWorkSteal
stealing.work_stealing_allowed = false
expect(async_profile_validate_v1(stealing)).to_equal(Err(AsyncProfileError.WorkStealingForbidden))
```

</details>

#### rejects mission allocation and pool escapes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var alloc = async_profile_mission_alloc_v1()
alloc.allocation_after_admission_allowed = true
expect(async_profile_validate_v1(alloc)).to_equal(Err(AsyncProfileError.MissionAllocViolation))
var pool = async_profile_mission_pool_v1()
pool.compiler_known_frame_bounds_required = false
expect(async_profile_validate_v1(pool)).to_equal(Err(AsyncProfileError.CompilerFrameBoundsRequired))
pool = async_profile_mission_pool_v1()
pool.detached_tasks_allowed = true
expect(async_profile_validate_v1(pool)).to_equal(Err(AsyncProfileError.DetachForbidden))
```

</details>

### AsyncProfile v1 canonical fingerprint

#### is sha256 of stable canonical text and changes with policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = async_profile_server_v1()
val first = async_profile_fingerprint_v1(original)
val second = async_profile_fingerprint_v1(async_profile_server_v1())
expect(first).to_equal(second)
expect(first).to_equal(sha256_text(async_profile_canonical_v1(original)))
var changed = async_profile_server_v1()
changed.instrumentation = AsyncInstrumentation.Profile
expect(async_profile_canonical_v1(original)).to_contain("|instrumentation=trace")
expect(async_profile_canonical_v1(changed)).to_contain("|instrumentation=profile")
expect(async_profile_fingerprint_v1(changed)).to_equal(
    sha256_text(async_profile_canonical_v1(changed)))
```

</details>

### AsyncProfile v1 exhaustive structural branches

#### rejects each identity and version contract independently

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = async_profile_common_v1()
p.schema_version = 2u16
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.UnsupportedSchema))
p = async_profile_common_v1()
p.profile_id = ""
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidIdentity))
p = async_profile_common_v1()
p.configuration_identity = "bad\nidentity"
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidIdentity))
p = async_profile_common_v1()
p.task_abi = "simple-task-frame-v2"
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidTaskAbi))
p = async_profile_common_v1()
p.ring_version = "simple-ring-v2"
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidRingVersion))
```

</details>

#### rejects every bounds lower, relation, and upper limit branch

<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = async_profile_common_v1()
p.bounds.max_tasks = 0u64
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidBounds))
p = async_profile_common_v1()
p.bounds.max_tasks = ASYNC_PROFILE_MAX_TASKS + 1u64
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidBounds))
p = async_profile_common_v1()
p.bounds.max_operations = p.bounds.max_tasks - 1u64
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidBounds))
p = async_profile_common_v1()
p.bounds.max_operations = ASYNC_PROFILE_MAX_OPERATIONS + 1u64
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidBounds))
p = async_profile_common_v1()
p.bounds.max_buffers = p.bounds.max_tasks - 1u64
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidBounds))
p = async_profile_common_v1()
p.bounds.max_buffers = ASYNC_PROFILE_MAX_BUFFERS + 1u64
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidBounds))
p = async_profile_common_v1()
p.bounds.max_traces = p.bounds.max_tasks - 1u64
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidBounds))
p = async_profile_common_v1()
p.bounds.max_traces = ASYNC_PROFILE_MAX_TRACES + 1u64
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidBounds))
p = async_profile_common_v1()
p.bounds.max_deadlines = p.bounds.max_tasks - 1u64
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidBounds))
p = async_profile_common_v1()
p.bounds.max_deadlines = ASYNC_PROFILE_MAX_DEADLINES + 1u64
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidBounds))
p = async_profile_common_v1()
p.bounds.max_poll_steps = 0u64
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidBounds))
p = async_profile_common_v1()
p.bounds.max_poll_steps = ASYNC_PROFILE_MAX_POLL_STEPS + 1u64
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidBounds))
```

</details>

#### rejects surface, scheduler-memory, mapping, and stealing contradictions

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = async_profile_common_v1()
p.surface = AsyncSurface.Off
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidSurfacePolicy))
p = async_profile_common_v1()
p.policy = AsyncPolicy.Forbidden
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidSurfacePolicy))
p = async_profile_common_v1()
p.scheduler = AsyncScheduler.ComputeWorkSteal
p.work_stealing_allowed = false
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.WorkStealingForbidden))
p = async_profile_common_v1()
p.memory = AsyncMemory.Static
p.placement = AsyncPlacement.Dynamic
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidSchedulerMemory))
p = async_profile_common_v1()
p.mapping = AsyncRingMapping.DirectRequired
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidMappingFallback))
```

</details>

### AsyncProfile v1 exhaustive mission branches

#### rejects invalid mission placement, memory, and blocking

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = async_profile_mission_alloc_v1()
p.placement = AsyncPlacement.Dynamic
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidMissionAssurance))
p = async_profile_mission_alloc_v1()
p.memory = AsyncMemory.Heap
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidMissionAssurance))
p = async_profile_mission_alloc_v1()
p.blocking_allowed = true
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.BlockingForbidden))
```

</details>

#### rejects each forbidden mission hot-path allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = async_profile_mission_alloc_v1()
p.allocation_in_isr_allowed = true
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.AllocationForbidden))
p = async_profile_mission_alloc_v1()
p.allocation_in_completion_allowed = true
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.AllocationForbidden))
p = async_profile_mission_alloc_v1()
p.allocation_in_durable_publication_allowed = true
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.AllocationForbidden))
```

</details>

#### rejects detach, fallback, stealing, nondeterminism, and unbounded polling

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = async_profile_mission_alloc_v1()
p.detached_tasks_allowed = true
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.DetachForbidden))
p = async_profile_mission_alloc_v1()
p.fallback_allowed = true
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidMappingFallback))
p = async_profile_mission_alloc_v1()
p.work_stealing_allowed = true
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.WorkStealingForbidden))
p = async_profile_mission_alloc_v1()
p.deterministic = false
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.DeterminismRequired))
p = async_profile_mission_alloc_v1()
p.unbounded_polling_allowed = true
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.UnboundedPollingForbidden))
```

</details>

#### rejects every mission_alloc and mission_pool preset escape

<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = async_profile_mission_alloc_v1()
p.allocation_after_admission_allowed = true
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.MissionAllocViolation))
p = async_profile_mission_alloc_v1()
p.scheduler = AsyncScheduler.Cooperative
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.MissionAllocViolation))
p = async_profile_mission_alloc_v1()
p.compiler_known_frame_bounds_required = true
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.MissionAllocViolation))
p = async_profile_mission_pool_v1()
p.memory = AsyncMemory.Arena
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.MissionPoolViolation))
p = async_profile_mission_pool_v1()
p.allocation_after_admission_allowed = true
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.MissionPoolViolation))
p = async_profile_mission_pool_v1()
p.scheduler = AsyncScheduler.Sharded
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.MissionPoolViolation))
p = async_profile_mission_pool_v1()
p.compiler_known_frame_bounds_required = false
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.CompilerFrameBoundsRequired))
p = async_profile_mission_pool_v1()
p.single_owner_mutable_queues_required = false
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.SingleOwnerQueueRequired))
```

</details>

#### rejects mission assurance paired with a non-mission preset

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = async_profile_common_v1()
p.assurance = AsyncAssurance.Mission
p.placement = AsyncPlacement.Static
p.memory = AsyncMemory.Arena
p.blocking_allowed = false
p.allocation_after_admission_allowed = false
p.detached_tasks_allowed = false
p.fallback_allowed = false
p.work_stealing_allowed = false
p.deterministic = true
p.unbounded_polling_allowed = false
expect(async_profile_validate_v1(p)).to_equal(Err(AsyncProfileError.InvalidMissionAssurance))
```

</details>

### AsyncProfile v1 exhaustive fingerprint sensitivity

#### distinguishes all five canonical presets

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val common = async_profile_common_v1()
val script = async_profile_script_v1()
val server = async_profile_server_v1()
val alloc = async_profile_mission_alloc_v1()
val pool = async_profile_mission_pool_v1()
expect(async_profile_fingerprint_v1(common) == async_profile_fingerprint_v1(script)).to_be(false)
expect(async_profile_fingerprint_v1(script) == async_profile_fingerprint_v1(server)).to_be(false)
expect(async_profile_fingerprint_v1(server) == async_profile_fingerprint_v1(alloc)).to_be(false)
expect(async_profile_fingerprint_v1(alloc) == async_profile_fingerprint_v1(pool)).to_be(false)
```

</details>

#### changes for every scalar identity, ABI, and enum field

<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = async_profile_common_v1()
var p = async_profile_common_v1()
p.schema_version = 2u16
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.preset = AsyncProfilePreset.Script
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.profile_id = "common-alt"
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.configuration_identity = "common-config-alt"
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.task_abi = "task-alt"
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.ring_version = "ring-alt"
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.surface = AsyncSurface.Explicit
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.policy = AsyncPolicy.RequiredForLatency
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.scheduler = AsyncScheduler.Ui
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.memory = AsyncMemory.Gc
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.mapping = AsyncRingMapping.EmulationAllowed
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.assurance = AsyncAssurance.Hardened
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.instrumentation = AsyncInstrumentation.Trace
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.placement = AsyncPlacement.Dynamic
expect_fingerprint_change(original, p)
```

</details>

#### changes for every resource bound

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = async_profile_common_v1()
var p = async_profile_common_v1()
p.bounds.max_tasks = p.bounds.max_tasks + 1u64
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.bounds.max_operations = p.bounds.max_operations + 1u64
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.bounds.max_buffers = p.bounds.max_buffers + 1u64
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.bounds.max_traces = p.bounds.max_traces + 1u64
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.bounds.max_deadlines = p.bounds.max_deadlines + 1u64
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.bounds.max_poll_steps = p.bounds.max_poll_steps + 1u64
expect_fingerprint_change(original, p)
```

</details>

#### changes for every boolean policy and evidence field

<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val original = async_profile_common_v1()
var p = async_profile_common_v1()
p.blocking_allowed = false
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.allocation_after_admission_allowed = false
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.allocation_in_isr_allowed = true
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.allocation_in_completion_allowed = true
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.allocation_in_durable_publication_allowed = true
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.detached_tasks_allowed = false
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.fallback_allowed = false
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.work_stealing_allowed = false
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.deterministic = true
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.compiler_known_frame_bounds_required = true
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.single_owner_mutable_queues_required = true
expect_fingerprint_change(original, p)
p = async_profile_common_v1()
p.unbounded_polling_allowed = false
expect_fingerprint_change(original, p)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/contracts/execution/async_profile_v1_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AsyncProfile v1 presets, AsyncProfile v1 fail-closed validation, AsyncProfile v1 canonical fingerprint, AsyncProfile v1 exhaustive structural branches, AsyncProfile v1 exhaustive mission branches, AsyncProfile v1 exhaustive fingerprint sensitivity.
- AsyncProfile v1 presets
- AsyncProfile v1 fail-closed validation
- AsyncProfile v1 canonical fingerprint
- AsyncProfile v1 exhaustive structural branches
- AsyncProfile v1 exhaustive mission branches
- AsyncProfile v1 exhaustive fingerprint sensitivity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `250439fd4d757bff06bff241cb75a237a74fef0888345b86bd1b91e9653e0da9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `250439fd4d757bff06bff241cb75a237a74fef0888345b86bd1b91e9653e0da9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `250439fd4d757bff06bff241cb75a237a74fef0888345b86bd1b91e9653e0da9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/01_unit/lib/common/contracts/execution/async_profile_v1_spec.spl
mirror: doc/06_spec/01_unit/lib/common/contracts/execution/async_profile_v1_spec.md (current)
findings: 10 blockers: 0
  narrative=80 structure=60 oracle=100
  traceability=80 evidence=100 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/contracts/execution/async_profile_v1_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/contracts/execution/async_profile_v1_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/contracts/execution/async_profile_v1_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/common/contracts/execution/async_profile_v1_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/01_unit/lib/common/contracts/execution/async_profile_v1_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/01_unit/lib/common/contracts/execution/async_profile_v1_spec.spl:1:1: warning SSDOC-TRC-001 [traceability] (-20): no implemented requirement identity
  why: Stable requirement identity connects intent, implementation, and evidence.
  improve: Bind scenarios to stable selected REQ identities.
test/01_unit/lib/common/contracts/execution/async_profile_v1_spec.spl:12:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'admits every canonical preset' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/contracts/execution/async_profile_v1_spec.spl:19:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'selects every named preset through the canonical selector' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/contracts/execution/async_profile_v1_spec.spl:27:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects malformed bounds and incompatible surface policy' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/contracts/execution/async_profile_v1_spec.spl:37:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'rejects direct mapping fallback and undeclared work stealing' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
