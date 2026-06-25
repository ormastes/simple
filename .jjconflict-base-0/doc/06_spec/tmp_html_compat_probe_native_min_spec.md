# Tmp Html Compat Probe Native Min Specification

> <details>

<!-- sdn-diagram:id=tmp_html_compat_probe_native_min_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_html_compat_probe_native_min_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_html_compat_probe_native_min_spec -> std
tmp_html_compat_probe_native_min_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_html_compat_probe_native_min_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Html Compat Probe Native Min Specification

## Scenarios

### html compat native probe min

#### renders one fixture through the probe

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val boxes = html_compat_fixture_simple_boxes("02_block_boxes", 320, 240)
expect(boxes.len()).to_equal(6)
expect(boxes[0].label).to_equal("outer")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `tmp_html_compat_probe_native_min_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- html compat native probe min

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
