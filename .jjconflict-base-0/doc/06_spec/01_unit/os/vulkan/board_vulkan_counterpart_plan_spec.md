# Board Vulkan Counterpart Plans and Backend Honesty

> The previous Vulkan plan for SimpleOS was built entirely on virtio-gpu/venus,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Board Vulkan Counterpart Plans and Backend Honesty

The previous Vulkan plan for SimpleOS was built entirely on virtio-gpu/venus,

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver |
| Status | In Progress |
| Plan | doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md |
| Source | `test/01_unit/os/vulkan/board_vulkan_counterpart_plan_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

The previous Vulkan plan for SimpleOS was built entirely on virtio-gpu/venus,
which is a VM device interface with no meaning on physical hardware. The reader
here is an engineer asking two questions: *does any backend claim board support
it has not earned*, and *when a backend does run, what is it compared against*.

This specification pins both answers as executable rules rather than prose.

## Scope and Preconditions

No GPU, board, or Mesa build is needed to run this file. It exercises the
backend profile table and the counterpart plan descriptors — the data that
decides what a later hardware run is allowed to conclude.

## Primary Workflow

Read the backend table, confirm nothing over-claims, then build the three
counterpart plans a SoC lane owns and confirm each is a valid plan that names an
independent open-source reference.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Board-runnable | Real silicon AND spirv+submit+readback implemented |
| venus | One backend, `qemu_only: true`, never board-runnable |
| Boundary | Where the Simple driver and the Mesa counterpart are compared |
| GPU receipt | Required only at the readback boundary — the one stage the CPU cannot honestly fake |

## Related Specifications

- [Counterpart relation matrix](../../infra/counterpart/relation_matrix_spec.spl) — how a plan is evaluated

## Evidence and Provenance

Executable against `src/os/drivers/gpu/board_vulkan/`. The refusal scenarios at
the end are the reason this file exists: they prove the honesty gate rejects an
over-claiming backend and a self-oracle plan.

## Recovery and Troubleshooting

A failure naming a SoC means that backend's profile claims a stage it has not
implemented. Implement the stage or lower the flag — do not relax the gate.

## Compatibility and Limitations

Today every board backend declares `spirv/submit/readback = false`, so
`board_vulkan_board_runnable_count` is legitimately zero. That zero is the
filed board gap, stated as a measurement instead of a note.

## Scenarios

### board vulkan backend table

#### registers one backend per SoC lane plus the QEMU backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
# @req REQ-BOARD-VULKAN-001
```

</details>

#### declares no capability any backend has not implemented

- run the honesty gate over every backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("run the honesty gate over every backend")
assert_equal(board_vulkan_backend_table_failures().len(), 0)
```

</details>

#### reports venus as never board-runnable

- evaluate the virtio/venus profile against the board rule


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("evaluate the virtio/venus profile against the board rule")
val venus = virtio_venus_board_profile()
assert_true(venus.qemu_only)
assert_false(board_profile_is_board_runnable(venus))
```

</details>

#### reports zero board-runnable backends today, which is the filed gap

- count board-runnable backends


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("count board-runnable backends")
assert_equal(board_runnable_count(), 0)
```

</details>

#### puts every counterpart in the one Mesa independence group they share

- compare independence groups across all four backends


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("compare independence groups across all four backends")
# Corrected 2026-08-11. Mesa's venus ICD is the guest-side counterpart for
# the venus backend, so it is `mesa` like turnip/anv/powervr — NOT a
# separate group. Grouping it apart double-counted references: a run using
# Mesa venus and Mesa anv would have claimed two independent oracles when
# there is one upstream tree. virglrenderer is the host-side transport, a
# different upstream, and is not installed here (lane L4 measured this).
for profile in board_vulkan_backends():
    assert_equal(profile.mesa_independence_group, "mesa")
```

</details>

#### therefore constitutes only ONE independent reference across all backends

- count distinct independence groups in the backend table


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("count distinct independence groups in the backend table")
var groups: [text] = []
for profile in board_vulkan_backends():
    var seen = false
    for existing in groups:
        if existing == profile.mesa_independence_group:
            seen = true
    if not seen:
        groups.push(profile.mesa_independence_group)
assert_equal(groups.len(), 1)
```

</details>

#### names the open-source counterpart for each board SoC

- read each board backend's counterpart


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read each board backend's counterpart")
assert_equal(adreno_board_profile().mesa_counterpart, "mesa-turnip")
assert_equal(img_bxe_board_profile().mesa_counterpart, "mesa-powervr")
assert_equal(intel_gen12_board_profile().mesa_counterpart, "mesa-anv")
```

</details>

#### marks a profile with its board-runnable verdict

- render the marker line


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("render the marker line")
assert_contains(board_profile_marker(adreno_board_profile()), "board_runnable=false")
```

</details>

### board vulkan counterpart plans

#### gives each SoC lane three boundaries to compare at

- build the plans for the Adreno lane


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build the plans for the Adreno lane")
assert_equal(board_vulkan_plans_for(adreno_board_profile(), "fixture:triangle").len(), 3)
```

</details>

#### accepts every generated plan as valid

- validate each plan fail-closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("validate each plan fail-closed")
for profile in board_vulkan_backends():
    for plan in board_vulkan_plans_for(profile, "fixture:triangle"):
        assert_equal(counterpart_plan_rejections(plan).len(), 0)
```

</details>

#### compares the Simple driver against an independent reference

- read the sources of the SPIR-V plan


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the sources of the SPIR-V plan")
val plan = board_vulkan_plan(
    intel_gen12_board_profile(),
    board_vulkan_boundary_spirv(),
    "fixture:triangle"
)
assert_equal(plan.sources.len(), 2)
assert_equal(plan.sources[0].source_id, board_vulkan_source_id_simple())
assert_equal(plan.sources[1].provider_id, "mesa-anv")
```

</details>

#### demands byte-exact agreement on the binary boundaries

- read the relation for spirv and cmdstream


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the relation for spirv and cmdstream")
assert_equal(relation_name(board_vulkan_relation_for(board_vulkan_boundary_spirv())), "byte_exact")
assert_equal(relation_name(board_vulkan_relation_for(board_vulkan_boundary_cmdstream())), "byte_exact")
```

</details>

#### demands an exact image on readback

- read the relation for readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the relation for readback")
assert_equal(relation_name(board_vulkan_relation_for(board_vulkan_boundary_readback())), "image_exact")
```

</details>

#### requires a device-origin GPU receipt only at the readback boundary

- read the GPU receipt requirement per boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the GPU receipt requirement per boundary")
assert_equal(board_vulkan_gpu_receipt_sources(board_vulkan_boundary_spirv()).len(), 0)
assert_equal(board_vulkan_gpu_receipt_sources(board_vulkan_boundary_readback()).len(), 1)
```

</details>

#### carries the board and kernel interface as the environment profile

- read the environment profile of the StarFive readback plan


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("read the environment profile of the StarFive readback plan")
val plan = board_vulkan_plan(
    img_bxe_board_profile(),
    board_vulkan_boundary_readback(),
    "fixture:triangle"
)
assert_equal(plan.environment_profile, "visionfive2/drm-powervr")
```

</details>

### board vulkan refusals

#### rejects a backend that claims submit without a SPIR-V encoder

- build a profile that skips a pipeline stage


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build a profile that skips a pipeline stage")
val lying = board_gpu_profile(
    "fake-soc", "fake-gpu", "mesa-anv", "mesa", "drm-i915", "fake-board",
    false, false, true, false
)
assert_true(board_profile_false_claim(lying))
assert_false(board_profile_is_board_runnable(lying))
```

</details>

#### rejects a QEMU-only backend that claims a physical board

- build a venus profile pointing at real hardware


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build a venus profile pointing at real hardware")
val lying = board_gpu_profile(
    "qemu-virtio", "venus", "virglrenderer-vtest", "virglrenderer",
    "virtio-gpu", "rb5", true, true, true, true
)
assert_true(board_profile_false_claim(lying))
assert_false(board_profile_is_board_runnable(lying))
```

</details>

#### rejects a plan whose only source is the Simple driver itself

- build a plan with no binding oracle


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("build a plan with no binding oracle")
val self_only = plan_source(
    board_vulkan_source_id_simple(), "simple.x", "gpu",
    OracleAuthority.self_execution_mode, true
)
val peer = plan_source(
    board_vulkan_source_id_counterpart(), "simple.y", "gpu",
    OracleAuthority.self_execution_mode, true
)
val plan = board_vulkan_plan(
    adreno_board_profile(), board_vulkan_boundary_spirv(), "fixture:triangle"
)
val sabotaged = CounterpartPlan(
    plan_id: plan.plan_id,
    boundary_id: plan.boundary_id,
    environment_profile: plan.environment_profile,
    input_ref: plan.input_ref,
    sources: [self_only, peer],
    comparisons: plan.comparisons,
    require_gpu_receipt_source_ids: plan.require_gpu_receipt_source_ids
)
assert_true(counterpart_plan_rejections(sabotaged).len() > 0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BOARD-VULKAN-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6c8b04a6a37d03f71b0f455786791f9a679fe64d1c941cceb87924e5be728768`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6c8b04a6a37d03f71b0f455786791f9a679fe64d1c941cceb87924e5be728768`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6c8b04a6a37d03f71b0f455786791f9a679fe64d1c941cceb87924e5be728768`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/os/vulkan/board_vulkan_counterpart_plan_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/board_vulkan_counterpart_plan_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=75
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/vulkan/board_vulkan_counterpart_plan_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/os/vulkan/board_vulkan_counterpart_plan_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/vulkan/board_vulkan_counterpart_plan_spec.spl:115:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'registers one backend per SoC lane plus the QEMU backend' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/vulkan/board_vulkan_counterpart_plan_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares no capability any backend has not implemented' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/board_vulkan_counterpart_plan_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports venus as never board-runnable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/board_vulkan_counterpart_plan_spec.spl:133:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports zero board-runnable backends today, which is the filed gap' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
