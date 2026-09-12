# Environment Variant Activation Specification

> Tests covering:

## Scenarios

### E5-001 serialized environment activation [importance=critical; importance_weight=3]

#### E5-001 should bind reference startup to an exact policy and environment receipt [importance=critical; importance_weight=3]

- Collect policy sources and resolve the effective ceiling


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-006
# @req REQ-014
step("Collect policy sources and resolve the effective ceiling")
collect_policy_sources()
resolve_policy_and_ceiling()
probe_execution_domain()
fail("MissingEvidence:E5-001:reference startup integration receipt; evidence-class=integration")
```

</details>

#### E5-001 should preserve scalar parity for an admitted x86 variant [importance=critical; importance_weight=3]

- Admit one exact artifact, pin its generation, and compare with scalar


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-002
# @req REQ-003
# @req REQ-010
step("Admit one exact artifact, pin its generation, and compare with scalar")
admit_exact_provider()
pin_selected_generation()
execute_bounded_region()
validate_completion_receipt()
```

</details>

#### E5-001 should reject stale or copied activation receipts [importance=critical; importance_weight=3]

- Replace the provider generation and validate the old receipt


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-004
# @req REQ-006
# @req REQ-014
step("Replace the provider generation and validate the old receipt")
pin_selected_generation()
fail("MissingEvidence:E5-001:stale-receipt invalidation owner; no copied handle may authorize a call")
drain_and_retire()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/environment_variant_activation_spec.spl` |
| Updated | 2026-09-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- E5-001 serialized environment activation [importance=critical; importance_weight=3]

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


<!-- sdn-diagram:id=environment_variant_activation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=environment_variant_activation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

environment_variant_activation_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=environment_variant_activation_spec.arch hash=sha256:auto
+-------------------------------------+      +-----+
| environment_variant_activation_spec | ---> | std |
+-------------------------------------+      +-----+
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |
