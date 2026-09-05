# NVIDIA Proprietary Independent Reference Gate (lane L5)

> Lane L4 measured that every Mesa Vulkan ICD on this host (anv, lavapipe,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# NVIDIA Proprietary Independent Reference Gate (lane L5)

Lane L4 measured that every Mesa Vulkan ICD on this host (anv, lavapipe,

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver |
| Status | In Progress |
| Plan | doc/03_plan/os/vulkan/board_vulkan_parallel_soc_lanes_2026-08-10.md |
| Source | `test/01_unit/os/vulkan/nvidia_independent_reference_gate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Lane L4 measured that every Mesa Vulkan ICD on this host (anv, lavapipe,
radv, nouveau, asahi, venus-guest) shares independence group `mesa`, so any
Vulkan boundary run whose executed sources are all drawn from that set is
one Mesa reference plus the Simple candidate — not two independent
references — and the frozen `counterpart_run_vacuity_failures` gate
correctly rejects it. This spec exercises the fix: NVIDIA's proprietary
driver, confirmed live on this host, as the second independent reference,
and the predicate that decides whether a concrete selection of executed
sources actually satisfies the independence gate.

The reader here is an engineer asking: *given the sources this run actually
executed, does the independence gate pass, and can an unavailable or
relabelled source fake a pass it hasn't earned?*

## Scope and Preconditions

No GPU submission and no board are needed to run this file — it exercises
pure `SourceResult` fixtures and the counting predicate over
`independence_group` and `ProviderStatus`. The underlying host measurement
(`nvidia-smi`, `VK_ICD_FILENAMES=... vulkaninfo --summary` enumerating two
discrete GPUs, `sha256sum` of the resolved `libGLX_nvidia.so.0` target) is
recorded as commentary in `provider_nvidia.spl`, not re-executed here.

## Primary Workflow

Build the manifest, confirm it passes `provider_manifest_rejections`, then
exercise `independence_gate_satisfied` over three selections: all-Mesa
(must fail), Mesa+NVIDIA both executed (must pass), and the two sabotage
selections that must be caught: NVIDIA relabelled into the `mesa` group, and
NVIDIA left `unavailable` in the selection.

## Key Concepts

| Concept | Description |
|---------|-------------|
| independence_group | What stops two wrappers over one engine counting as two references |
| ProviderStatus.executed | Only executed sources may count toward independence |
| independence_gate_satisfied | >= 2 distinct independence groups among EXECUTED sources |
| nvidia-proprietary | The only genuinely independent second reference on this host |

## Related Specifications

- [Provider inventory](provider_inventory_spec.spl) — the static `ProviderManifest` identity layer this gate builds on

## Evidence and Provenance

Executable against `src/os/drivers/gpu/board_vulkan/provider_nvidia.spl`.
The sabotage scenarios are the reason this file exists: an `unavailable`
source, or one relabelled to hide inside `mesa`, must never let a
one-reference selection pass as two.

## Recovery and Troubleshooting

A failure naming the manifest gate means NVIDIA's measured identity
(hash/version) is stale — remeasure with `sha256sum` against the currently
installed driver. A failure in the gate predicates themselves is a real
regression in the independence rule, not a measurement problem.

## Compatibility and Limitations

This spec does not open a Vulkan device or submit work; it is the pure
identity + counting layer. Real device enumeration is recorded as measured
commentary in `provider_nvidia.spl`, taken with `vulkaninfo` pinned to
`nvidia_icd.json` via `VK_ICD_FILENAMES` on this host on 2026-08-11.

## Scenarios

### NVIDIA proprietary independent reference gate

#### measures NVIDIA proprietary as a well-formed manifest with a real hash and proprietary license

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
# @req REQ-BOARD-VULKAN-001
```

</details>

#### rejects an all-Mesa selection as one-reference-only regardless of how many Mesa sources are present

- select the candidate plus one Mesa reference
- select the candidate plus every Mesa reference this host has


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("select the candidate plus one Mesa reference")
val one_mesa = [
    simple_candidate_source(ProviderStatus.executed),
    mesa_reference_source("anv", ProviderStatus.executed)
]
assert_equal(independence_gate_executed_group_count(one_mesa), 1)
assert_false(independence_gate_satisfied(one_mesa))

step("select the candidate plus every Mesa reference this host has")
val all_mesa = [
    simple_candidate_source(ProviderStatus.executed),
    mesa_reference_source("anv", ProviderStatus.executed),
    mesa_reference_source("lavapipe", ProviderStatus.executed),
    mesa_reference_source("radv", ProviderStatus.executed),
    mesa_reference_source("nouveau", ProviderStatus.executed),
    mesa_reference_source("asahi", ProviderStatus.executed),
    mesa_reference_source("venus-guest", ProviderStatus.executed)
]
assert_equal(independence_gate_executed_group_count(all_mesa), 1)
assert_false(independence_gate_satisfied(all_mesa))
```

</details>

#### passes when the candidate, one Mesa reference, and NVIDIA are all executed

- select candidate + one Mesa + NVIDIA, all genuinely executed


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("select candidate + one Mesa + NVIDIA, all genuinely executed")
val selection = [
    simple_candidate_source(ProviderStatus.executed),
    mesa_reference_source("anv", ProviderStatus.executed),
    nvidia_reference_source(ProviderStatus.executed, INDEPENDENCE_GROUP_NVIDIA_PROPRIETARY)
]
assert_equal(independence_gate_executed_group_count(selection), 2)
assert_true(independence_gate_satisfied(selection))
```

</details>

### NVIDIA proprietary independent reference gate — sabotage proofs

#### sabotage (a): relabelling NVIDIA's independence_group to mesa is caught as one-reference-only

- the honest selection passes: mesa and nvidia-proprietary are two distinct groups
- relabel NVIDIA's independence_group into mesa, faking non-independence
- the gate correctly reports this selection as one-reference-only


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("the honest selection passes: mesa and nvidia-proprietary are two distinct groups")
val honest = [
    simple_candidate_source(ProviderStatus.executed),
    mesa_reference_source("anv", ProviderStatus.executed),
    nvidia_reference_source(ProviderStatus.executed, INDEPENDENCE_GROUP_NVIDIA_PROPRIETARY)
]
assert_true(independence_gate_satisfied(honest))

step("relabel NVIDIA's independence_group into mesa, faking non-independence")
val sabotaged = [
    simple_candidate_source(ProviderStatus.executed),
    mesa_reference_source("anv", ProviderStatus.executed),
    nvidia_reference_source(ProviderStatus.executed, INDEPENDENCE_GROUP_MESA)
]
step("the gate correctly reports this selection as one-reference-only")
assert_equal(independence_gate_executed_group_count(sabotaged), 1)
assert_false(independence_gate_satisfied(sabotaged))
assert_true(independence_gate_satisfied(honest) != independence_gate_satisfied(sabotaged))
```

</details>

#### sabotage (b): an unavailable NVIDIA source never counts toward independence, even left in the selection

- the honest selection passes with NVIDIA executed
- mark NVIDIA's source status unavailable while leaving it in the selection
- the gate does not count the unavailable source toward independence


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("the honest selection passes with NVIDIA executed")
val honest = [
    simple_candidate_source(ProviderStatus.executed),
    mesa_reference_source("anv", ProviderStatus.executed),
    nvidia_reference_source(ProviderStatus.executed, INDEPENDENCE_GROUP_NVIDIA_PROPRIETARY)
]
assert_true(independence_gate_satisfied(honest))

step("mark NVIDIA's source status unavailable while leaving it in the selection")
val sabotaged = [
    simple_candidate_source(ProviderStatus.executed),
    mesa_reference_source("anv", ProviderStatus.executed),
    nvidia_reference_source(ProviderStatus.unavailable, INDEPENDENCE_GROUP_NVIDIA_PROPRIETARY)
]
step("the gate does not count the unavailable source toward independence")
assert_equal(independence_gate_executed_group_count(sabotaged), 1)
assert_false(independence_gate_satisfied(sabotaged))
assert_true(independence_gate_satisfied(honest) != independence_gate_satisfied(sabotaged))
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

- Canonical SPipe generation for source `c2ac53ed1d9b8acbb64cde7f10cfc558c69e98396e73fc47aad4a4b8515f6253`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c2ac53ed1d9b8acbb64cde7f10cfc558c69e98396e73fc47aad4a4b8515f6253`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c2ac53ed1d9b8acbb64cde7f10cfc558c69e98396e73fc47aad4a4b8515f6253`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/os/vulkan/nvidia_independent_reference_gate_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/nvidia_independent_reference_gate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=75
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/vulkan/nvidia_independent_reference_gate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/os/vulkan/nvidia_independent_reference_gate_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/vulkan/nvidia_independent_reference_gate_spec.spl:104:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'measures NVIDIA proprietary as a well-formed manifest with a real hash and proprietary license' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/vulkan/nvidia_independent_reference_gate_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an all-Mesa selection as one-reference-only regardless of how many Mesa sources are present' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/nvidia_independent_reference_gate_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes when the candidate, one Mesa reference, and NVIDIA are all executed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/nvidia_independent_reference_gate_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sabotage (a): relabelling NVIDIA's independence_group to mesa is caught as one-reference-only' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
