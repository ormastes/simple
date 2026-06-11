# Tmp Html Compat Core Native Specification

> <details>

<!-- sdn-diagram:id=tmp_html_compat_core_native_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_html_compat_core_native_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_html_compat_core_native_spec -> std
tmp_html_compat_core_native_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_html_compat_core_native_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Html Compat Core Native Specification

## Scenarios

### html compat core native

#### renders core boxes without the compare bridge

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val boxes = html_compat_fixture_simple_boxes("24_flex_wrap_reverse_basic", 320, 240)
expect(boxes.len()).to_equal(4)
expect(boxes[0].label).to_equal("wrap_reverse_shell")
expect(boxes[1].y).to_equal(40)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `tmp_html_compat_core_native_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- html compat core native

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
