# Detection: grouping-key confusion in independence-style gates

> This spec generalizes past one incident to the DEFECT CLASS behind it: a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Detection: grouping-key confusion in independence-style gates

This spec generalizes past one incident to the DEFECT CLASS behind it: a

## At a Glance

| Field | Value |
|-------|-------|
| Category | OS / GPU driver |
| Status | In Progress |
| Source | `test/01_unit/os/vulkan/independence_gate_key_confusion_detection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

This spec generalizes past one incident to the DEFECT CLASS behind it: a
gate that is documented to aggregate on a *semantic family* field but is
implemented to aggregate on a *per-instance identity* field. Such a gate is
silently fail-open — it over-counts, and over-counting is always the unsafe
direction for an independence predicate.

The class is detected by two paired properties that no identity-keyed
implementation can satisfy simultaneously:

1. **Collapse.** Sources sharing a family must count once no matter how
   many distinct identities they carry. An identity-keyed gate over-counts.
2. **Separation.** Sources sharing an identity but differing in family must
   count separately. An identity-keyed gate under-counts.

Any single-field implementation that passes (1) by keying on the family
field will also pass (2); an implementation keying on identity fails both.
The two together therefore pin the key rather than the arithmetic.

## Scope and Preconditions

Pure predicate-level, in-process. No GPU, no subprocess, no device.

## Primary Workflow

Construct adversarial selections that vary identity and family
independently, and assert the count tracks family only.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Collapse property | same family, many identities => 1 |
| Separation property | same identity, many families => n |
| Fail-open | over-counting independent references |

## Related Specifications

- [Independence group key regression](independence_group_key_regression_spec.spl) — the concrete reproducer

## Evidence and Provenance

Derived from `independence_gate_executed_group_count` in
`src/os/drivers/gpu/board_vulkan/provider_nvidia.spl`.

## Recovery and Troubleshooting

A RED on the separation property with a GREEN collapse (or vice versa) means
the gate keys on the wrong field; fix the key, not the counts.

## Compatibility and Limitations

Covers the grouping-key axis only; status filtering is covered by the lane
spec's sabotage (b).

## Scenarios

### independence gate — grouping-key confusion detection

#### collapse property: identical family with maximally distinct identities counts once

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
# @req REQ-BOARD-VULKAN-003
```

</details>

#### separation property: identical identity with distinct families counts separately

- two sources share provider_id host-nvidia-proprietary but differ in family
- an identity-keyed gate would under-count this selection as 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("two sources share provider_id host-nvidia-proprietary but differ in family")
val two_families = [
    nvidia_reference_source(ProviderStatus.executed, INDEPENDENCE_GROUP_NVIDIA_PROPRIETARY),
    nvidia_reference_source(ProviderStatus.executed, INDEPENDENCE_GROUP_MESA)
]
step("an identity-keyed gate would under-count this selection as 1")
assert_equal(independence_gate_executed_group_count(two_families), 2)
```

</details>

#### the two properties disagree for any identity-keyed implementation

- collapse case: 6 identities, 1 family
- separation case: 1 identity, 2 families
- family-keyed is the only assignment satisfying both at once


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("collapse case: 6 identities, 1 family")
val collapse = [
    mesa_reference_source("anv", ProviderStatus.executed),
    mesa_reference_source("lavapipe", ProviderStatus.executed),
    mesa_reference_source("radv", ProviderStatus.executed),
    mesa_reference_source("nouveau", ProviderStatus.executed),
    mesa_reference_source("asahi", ProviderStatus.executed),
    mesa_reference_source("venus-guest", ProviderStatus.executed)
]
step("separation case: 1 identity, 2 families")
val separation = [
    nvidia_reference_source(ProviderStatus.executed, INDEPENDENCE_GROUP_NVIDIA_PROPRIETARY),
    nvidia_reference_source(ProviderStatus.executed, INDEPENDENCE_GROUP_MESA)
]
step("family-keyed is the only assignment satisfying both at once")
assert_equal(independence_gate_executed_group_count(collapse), 1)
assert_equal(independence_gate_executed_group_count(separation), 2)
assert_true(
    independence_gate_executed_group_count(collapse)
        < independence_gate_executed_group_count(separation)
)
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
- `REQ-BOARD-VULKAN-003`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9efee772b2313a9c1b6561f0d00e8e17d98f096f88d3ea0b43a1b588529d8751`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9efee772b2313a9c1b6561f0d00e8e17d98f096f88d3ea0b43a1b588529d8751`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9efee772b2313a9c1b6561f0d00e8e17d98f096f88d3ea0b43a1b588529d8751`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/01_unit/os/vulkan/independence_gate_key_confusion_detection_spec.spl
mirror: doc/06_spec/01_unit/os/vulkan/independence_gate_key_confusion_detection_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=75
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/vulkan/independence_gate_key_confusion_detection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/01_unit/os/vulkan/independence_gate_key_confusion_detection_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/os/vulkan/independence_gate_key_confusion_detection_spec.spl:86:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'collapse property: identical family with maximally distinct identities counts once' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/os/vulkan/independence_gate_key_confusion_detection_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'separation property: identical identity with distinct families counts separately' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/vulkan/independence_gate_key_confusion_detection_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the two properties disagree for any identity-keyed implementation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
