# Independence gate must group by `independence_group`, never by `provider_id`

> `independence_gate_executed_group_count` exists to answer one question: how

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Independence gate must group by `independence_group`, never by `provider_id`

`independence_gate_executed_group_count` exists to answer one question: how

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver |
| Status | In Progress |
| Source | `test/01_unit/os/vulkan/independence_group_key_regression_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

`independence_gate_executed_group_count` exists to answer one question: how
many INDEPENDENT implementations actually executed for this boundary run.
Independence is carried by `SourceResult.independence_group` — every Mesa
ICD (anv, lavapipe, radv, nouveau, asahi, venus-guest) collapses to the
single group `mesa` no matter how many distinct `provider_id`s they carry.

This spec is the reproducing regression for a fail-open in which the gate
keyed on `provider_id` instead. Under that defect any two differently-named
providers satisfied the gate, so six Mesa ICDs counted as six independent
references and a source whose `independence_group` was relabelled into
`mesa` still counted as independent — defeating the exact sabotage the gate
was built to catch.

## Scope and Preconditions

Pure predicate-level. No GPU, no subprocess, no device is required: the
selections are constructed in-process from the lane's own source builders.

## Primary Workflow

Build selections that differ ONLY in `independence_group` while keeping
`provider_id` distinct, and require the gate's count to follow the group,
not the id.

## Key Concepts

| Concept | Description |
|---------|-------------|
| independence_group | The implementation-family key; the only valid grouping key |
| provider_id | A per-source name; distinct even within one family |
| executed | Only `ProviderStatus.executed` sources may count |

## Related Specifications

- [NVIDIA independent reference gate](nvidia_independent_reference_gate_spec.spl) — the lane spec this regression protects

## Evidence and Provenance

Derived from a direct read of `independence_gate_executed_group_count` in
`src/os/drivers/gpu/board_vulkan/provider_nvidia.spl`, whose own doc comment
describes grouping by `independence_group` while the body grouped by
`provider_id`.

## Recovery and Troubleshooting

A RED here means the gate is fail-open and every "two independent
references" verdict produced by a board-Vulkan boundary run is unsound.

## Compatibility and Limitations

Predicate-level only; it does not assert that any counterpart actually ran.

## Scenarios

### independence gate grouping key

#### counts many distinctly-named Mesa providers as exactly one independent group

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
# @req REQ-BOARD-VULKAN-002
```

</details>

#### does not let the candidate's empty independence_group count as a group

- candidate alone has an empty independence_group
- candidate plus one Mesa reference is still one independent group


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("candidate alone has an empty independence_group")
val candidate_only = [simple_candidate_source(ProviderStatus.executed)]
assert_equal(independence_gate_executed_group_count(candidate_only), 0)

step("candidate plus one Mesa reference is still one independent group")
val candidate_plus_mesa = [
    simple_candidate_source(ProviderStatus.executed),
    mesa_reference_source("anv", ProviderStatus.executed)
]
assert_equal(independence_gate_executed_group_count(candidate_plus_mesa), 1)
assert_false(independence_gate_satisfied(candidate_plus_mesa))
```

</details>

#### collapses a source relabelled into mesa even though its provider_id stays unique

- honest selection: mesa + nvidia-proprietary are two groups
- relabel only the group; provider_id host-nvidia-proprietary is untouched
- a provider_id-keyed gate would still say 2 here; a correct gate says 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("honest selection: mesa + nvidia-proprietary are two groups")
val honest = [
    simple_candidate_source(ProviderStatus.executed),
    mesa_reference_source("anv", ProviderStatus.executed),
    nvidia_reference_source(ProviderStatus.executed, INDEPENDENCE_GROUP_NVIDIA_PROPRIETARY)
]
assert_equal(independence_gate_executed_group_count(honest), 2)
assert_true(independence_gate_satisfied(honest))

step("relabel only the group; provider_id host-nvidia-proprietary is untouched")
val relabelled = [
    simple_candidate_source(ProviderStatus.executed),
    mesa_reference_source("anv", ProviderStatus.executed),
    nvidia_reference_source(ProviderStatus.executed, INDEPENDENCE_GROUP_MESA)
]
step("a provider_id-keyed gate would still say 2 here; a correct gate says 1")
assert_equal(independence_gate_executed_group_count(relabelled), 1)
assert_false(independence_gate_satisfied(relabelled))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-BOARD-VULKAN-002`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `741c6a85e39b1d11e176a139a413f80866d3d1678aeff26f9bf6b8ccbe26f856`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `741c6a85e39b1d11e176a139a413f80866d3d1678aeff26f9bf6b8ccbe26f856`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `741c6a85e39b1d11e176a139a413f80866d3d1678aeff26f9bf6b8ccbe26f856`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/01_unit/os/vulkan/independence_group_key_regression_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/independence_group_key_regression_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=75
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/vulkan/independence_group_key_regression_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/os/vulkan/independence_group_key_regression_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/vulkan/independence_group_key_regression_spec.spl:87:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'counts many distinctly-named Mesa providers as exactly one independent group' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/vulkan/independence_group_key_regression_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not let the candidate's empty independence_group count as a group' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/independence_group_key_regression_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collapses a source relabelled into mesa even though its provider_id stays unique' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
