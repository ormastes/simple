# Simple Web Qemu Panel Specification

> <details>

<!-- sdn-diagram:id=simple_web_qemu_panel_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_qemu_panel_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_qemu_panel_spec -> std
simple_web_qemu_panel_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_qemu_panel_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Qemu Panel Specification

## Scenarios

### SimpleOS QEMU Simple Web panel contract

#### keeps the browser panel tied to Simple Web HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = qemu_simple_web_demo_html()
expect(html).to_contain("about:engine2d-wm")
expect(html).to_contain("Simple Web Renderer")
expect(html).to_contain("HTML -> layout -> paint -> pixels -> Engine2D")
```

</details>

#### maps HTML bands to deterministic panel colors

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(qemu_simple_web_panel_color_at(0, 0)).to_equal(0xFF2050A0u32)
expect(qemu_simple_web_panel_color_at(7, 7)).to_equal(0xFFFFFFFFu32)
expect(qemu_simple_web_panel_color_at(4, 7)).to_equal(0xFF2050A0u32)
expect(qemu_simple_web_panel_color_at(0, 30)).to_equal(0xFF182230u32)
expect(qemu_simple_web_panel_color_at(0, 116)).to_equal(0xFF1F2937u32)
expect(qemu_simple_web_panel_color_at(0, 202)).to_equal(0xFF101820u32)
```

</details>

#### emits stable pixel count and checksum evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(qemu_simple_web_panel_pixel_count(248, 118)).to_equal(29264)
expect(qemu_simple_web_panel_pixel_count(270, 114)).to_equal(30780)
expect(qemu_simple_web_panel_checksum(8, 8)).to_be_greater_than(0)
expect(qemu_simple_web_panel_checksum(248, 118)).to_equal(qemu_simple_web_panel_checksum(248, 118))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/simple_web_qemu_panel_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS QEMU Simple Web panel contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
