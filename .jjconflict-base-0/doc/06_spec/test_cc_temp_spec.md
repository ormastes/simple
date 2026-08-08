# Test Cc Temp Specification

> <details>

<!-- sdn-diagram:id=test_cc_temp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_cc_temp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_cc_temp_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_cc_temp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Cc Temp Specification

## Scenarios

### color_after

#### test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 80px; height: 40px; background-color: currentColor; color: #456789'></div></body></html>"
expect(_sfcc(html, 0xFF456789u32)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/test_cc_temp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- color_after

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
