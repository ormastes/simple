# All Modes Cross-Mode Tests

> Verifies that tests without a `@mode` annotation run correctly in all execution modes.

<!-- sdn-diagram:id=all_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=all_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

all_modes_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=all_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# All Modes Cross-Mode Tests

Verifies that tests without a `@mode` annotation run correctly in all execution modes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing Framework |
| Status | Active |
| Source | `test/03_system/feature/mode_filter/all_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that tests without a `@mode` annotation run correctly in all execution modes.

## Scenarios

### Cross-mode tests

#### arithmetic works everywhere

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(2 + 3).to_equal(5)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
