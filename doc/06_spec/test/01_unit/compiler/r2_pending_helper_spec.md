# R2 Pending Helper Specification

> 1. pending

<!-- sdn-diagram:id=r2_pending_helper_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=r2_pending_helper_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

r2_pending_helper_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=r2_pending_helper_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# R2 Pending Helper Specification

## Scenarios

### R2 pending helper

#### marks a TODO test as pending without running its body

1. pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The interpreter BDD hook recognizes `pending` and prints
# "○ <name> (skipped)" in yellow. The test does not fail.
pending("reserved for future crypto KAT — see R2")
```

</details>

#### regular tests next to pending tests still run

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(2 + 2).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/r2_pending_helper_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- R2 pending helper

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
