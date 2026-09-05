# Simple Ring Profile Integration Specification

> Tests covering SimpleRing profile integration matrix.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Ring Profile Integration Specification

## Scenarios

### SimpleRing profile integration matrix

#### integrates all five canonical presets with their execution policies

- exercise integrates all five canonical presets with their execution policies
   - Expected: common.surface equals `AsyncSurface.Implicit`
   - Expected: common.scheduler equals `AsyncScheduler.Hybrid`
   - Expected: script.scheduler equals `AsyncScheduler.Ui`
   - Expected: script.memory equals `AsyncMemory.Gc`
   - Expected: server.policy equals `AsyncPolicy.RequiredForLatency`
   - Expected: server.scheduler equals `AsyncScheduler.Sharded`
   - Expected: server.assurance equals `AsyncAssurance.Hardened`
   - Expected: mission_alloc.memory equals `AsyncMemory.Arena`
   - Expected: mission_alloc.scheduler equals `AsyncScheduler.FixedPriority`
   - Expected: mission_pool.memory equals `AsyncMemory.Pool`
   - Expected: mission_pool.scheduler equals `AsyncScheduler.Cooperative`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("exercise integrates all five canonical presets with their execution policies")
val common = async_profile_preset_v1(AsyncProfilePreset.Common)
val script = async_profile_preset_v1(AsyncProfilePreset.Script)
val server = async_profile_preset_v1(AsyncProfilePreset.Server)
val mission_alloc = async_profile_preset_v1(AsyncProfilePreset.MissionAlloc)
val mission_pool = async_profile_preset_v1(AsyncProfilePreset.MissionPool)
expect_valid_profile(common, "common")
expect_valid_profile(script, "script")
expect_valid_profile(server, "server")
expect_valid_profile(mission_alloc, "mission_alloc")
expect_valid_profile(mission_pool, "mission_pool")
expect(common.surface).to_equal(AsyncSurface.Implicit)
expect(common.scheduler).to_equal(AsyncScheduler.Hybrid)
expect(script.scheduler).to_equal(AsyncScheduler.Ui)
expect(script.memory).to_equal(AsyncMemory.Gc)
expect(server.policy).to_equal(AsyncPolicy.RequiredForLatency)
expect(server.scheduler).to_equal(AsyncScheduler.Sharded)
expect(server.assurance).to_equal(AsyncAssurance.Hardened)
expect(mission_alloc.memory).to_equal(AsyncMemory.Arena)
expect(mission_alloc.scheduler).to_equal(AsyncScheduler.FixedPriority)
expect(mission_pool.memory).to_equal(AsyncMemory.Pool)
expect(mission_pool.scheduler).to_equal(AsyncScheduler.Cooperative)
```

</details>

#### admits hosted profiles and rejects both direct-required mission profiles

- exercise admits hosted profiles and rejects both direct-required mission profiles
   - Expected: common.mapping equals `RingMappingGrade.Software`
   - Expected: common.requested_depth equals `8`
   - Expected: server.requested_depth equals `32`
   - Expected: provider.counters().admissions equals `3u64`
   - Expected: provider.counters().rejections equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("exercise admits hosted profiles and rejects both direct-required mission profiles")
val provider = match SoftwareRingProvider<i64, i64>.create(7301u64, 32):
    case Ok(value): value
    case Err(_): fail("profile provider construction failed")
val common = provider.admit_for_depth(async_profile_common_v1(), 8)
val script = provider.admit_for_depth(async_profile_script_v1(), 8)
val server = provider.admit_for_depth(async_profile_server_v1(), 32)
match common.status:
    case SoftwareProviderAdmissionStatus.Admitted:
        expect(common.mapping).to_equal(RingMappingGrade.Software)
        expect(common.requested_depth).to_equal(8)  # oracle: common.requested_depth must equal 8 — authoritative contract constant
    case SoftwareProviderAdmissionStatus.Rejected: fail("common rejected")
match script.status:
    case SoftwareProviderAdmissionStatus.Admitted: ()
    case SoftwareProviderAdmissionStatus.Rejected: fail("script rejected")
match server.status:
    case SoftwareProviderAdmissionStatus.Admitted:
        expect(server.requested_depth).to_equal(32)  # oracle: server.requested_depth must equal 32 — authoritative contract constant
    case SoftwareProviderAdmissionStatus.Rejected: fail("server rejected")
val mission_alloc = provider.admit(async_profile_mission_alloc_v1())
val mission_pool = provider.admit(async_profile_mission_pool_v1())
match mission_alloc.status:
    case SoftwareProviderAdmissionStatus.Rejected:
        expect(mission_alloc.fallback_reason).to_equal(
            "direct ring mapping required")
    case SoftwareProviderAdmissionStatus.Admitted:
        fail("mission_alloc software mapping admitted")
match mission_pool.status:
    case SoftwareProviderAdmissionStatus.Rejected:
        expect(mission_pool.fallback_reason).to_equal(
            "direct ring mapping required")
    case SoftwareProviderAdmissionStatus.Admitted:
        fail("mission_pool software mapping admitted")
expect(provider.counters().admissions).to_equal(3u64)
expect(provider.counters().rejections).to_equal(2u64)
```

</details>

#### keeps every preset fingerprint distinct and stable across reconstruction

- exercise keeps every preset fingerprint distinct and stable across reconstruction
   - Expected: common equals `async_profile_fingerprint_v1(async_profile_common_v1())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("exercise keeps every preset fingerprint distinct and stable across reconstruction")
val common = async_profile_fingerprint_v1(async_profile_common_v1())
val script = async_profile_fingerprint_v1(async_profile_script_v1())
val server = async_profile_fingerprint_v1(async_profile_server_v1())
val mission_alloc = async_profile_fingerprint_v1(
    async_profile_mission_alloc_v1())
val mission_pool = async_profile_fingerprint_v1(
    async_profile_mission_pool_v1())
expect(common).to_equal(async_profile_fingerprint_v1(async_profile_common_v1()))
expect(script == common).to_be(false)
expect(server == common).to_be(false)
expect(mission_alloc == common).to_be(false)
expect(mission_pool == common).to_be(false)
expect(server == script).to_be(false)
expect(mission_alloc == mission_pool).to_be(false)
```

</details>

#### preserves mission fail-closed policy at the integration boundary

- exercise preserves mission fail-closed policy at the integration boundary
   - Expected: mission_alloc.mapping equals `AsyncRingMapping.DirectRequired`
   - Expected: mission_pool.mapping equals `AsyncRingMapping.DirectRequired`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("exercise preserves mission fail-closed policy at the integration boundary")
val mission_alloc = async_profile_mission_alloc_v1()
val mission_pool = async_profile_mission_pool_v1()
expect(mission_alloc.mapping).to_equal(AsyncRingMapping.DirectRequired)
expect(mission_pool.mapping).to_equal(AsyncRingMapping.DirectRequired)
expect(mission_alloc.blocking_allowed).to_be(false)
expect(mission_pool.blocking_allowed).to_be(false)
expect(mission_alloc.allocation_after_admission_allowed).to_be(false)
expect(mission_pool.allocation_after_admission_allowed).to_be(false)
expect(mission_alloc.detached_tasks_allowed).to_be(false)
expect(mission_pool.detached_tasks_allowed).to_be(false)
expect(mission_alloc.deterministic).to_be(true)
expect(mission_pool.deterministic).to_be(true)
expect(mission_alloc.unbounded_polling_allowed).to_be(false)
expect(mission_pool.unbounded_polling_allowed).to_be(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/async/simple_ring_profile_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleRing profile integration matrix.
- SimpleRing profile integration matrix

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b6b848a088567634d8f7b3be620f28305e0285c80bf8985b68de93e09763fcd4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b6b848a088567634d8f7b3be620f28305e0285c80bf8985b68de93e09763fcd4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b6b848a088567634d8f7b3be620f28305e0285c80bf8985b68de93e09763fcd4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/02_integration/lib/async/simple_ring_profile_integration_spec.spl
mirror: doc/06_spec/02_integration/lib/async/simple_ring_profile_integration_spec.md (current)
findings: 9 blockers: 0
  narrative=80 structure=100 oracle=100
  traceability=80 evidence=70 coverage=100 maintainability=45
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/async/simple_ring_profile_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/async/simple_ring_profile_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, traceability, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/lib/async/simple_ring_profile_integration_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/02_integration/lib/async/simple_ring_profile_integration_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/02_integration/lib/async/simple_ring_profile_integration_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/02_integration/lib/async/simple_ring_profile_integration_spec.spl:1:1: warning SSDOC-TRC-001 [traceability] (-20): no implemented requirement identity
  why: Stable requirement identity connects intent, implementation, and evidence.
  improve: Bind scenarios to stable selected REQ identities.
test/02_integration/lib/async/simple_ring_profile_integration_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'integrates all five canonical presets with their execution policies' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/async/simple_ring_profile_integration_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'admits hosted profiles and rejects both direct-required mission profiles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/lib/async/simple_ring_profile_integration_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps every preset fingerprint distinct and stable across reconstruction' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
