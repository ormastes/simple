# Lean E2e Specification

> <details>

<!-- sdn-diagram:id=lean_e2e_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lean_e2e_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lean_e2e_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lean_e2e_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lean E2e Specification

## Scenarios

### Lean verification portable smoke

#### records proof generation stages

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stages = ["fingerprint", "cache", "emit", "check"]
expect(stages.len()).to_equal(4)
expect(stages[0]).to_equal("fingerprint")
```

</details>

#### records Lean output extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "build/verification/proof.lean"
expect(path).to_end_with(".lean")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/verification/lean_e2e_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Lean verification portable smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
