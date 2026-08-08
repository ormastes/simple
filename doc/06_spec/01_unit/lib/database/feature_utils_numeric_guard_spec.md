# Feature Utils Numeric Guard Specification

> <details>

<!-- sdn-diagram:id=feature_utils_numeric_guard_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=feature_utils_numeric_guard_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

feature_utils_numeric_guard_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=feature_utils_numeric_guard_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Feature Utils Numeric Guard Specification

## Scenarios

### database feature utils numeric guard

#### falls back when feature id integer parsing overflows

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sync_source = rt_file_read_text("src/lib/nogc_sync_mut/database/feature_utils.spl") ?? ""
val async_source = rt_file_read_text("src/lib/nogc_async_mut/database/feature_utils.spl") ?? ""

expect(sync_source).to_contain("s.to_int() ?? default")
expect(async_source).to_contain("s.to_int() ?? default")
expect(sync_source.contains("s.to_int()\n")).to_equal(false)
expect(async_source.contains("s.to_int()\n")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/database/feature_utils_numeric_guard_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- database feature utils numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
