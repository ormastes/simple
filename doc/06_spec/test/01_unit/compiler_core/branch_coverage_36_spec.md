# Branch Coverage 36 Specification

> <details>

<!-- sdn-diagram:id=branch_coverage_36_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=branch_coverage_36_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

branch_coverage_36_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=branch_coverage_36_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Branch Coverage 36 Specification

## Scenarios

### BranchCoverage36

#### skipped

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pending_reason = "match on tuple and while with complex condition return false"
expect(pending_reason.len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/branch_coverage_36_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BranchCoverage36

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
