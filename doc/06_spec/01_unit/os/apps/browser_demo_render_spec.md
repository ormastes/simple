# Browser Demo Render Specification

> <details>

<!-- sdn-diagram:id=browser_demo_render_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_demo_render_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_demo_render_spec -> std
browser_demo_render_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_demo_render_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Demo Render Specification

## Scenarios

### Browser Demo rendering

#### precomputes browser render stats for the desktop app tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app = BrowserDemoApp.new()
expect(app.render_done).to_equal(true)
expect(app.node_count).to_be_greater_than(0)
expect(app.pixel_count).to_be_greater_than(0)
```

</details>

#### renders non-background pixels through the browser engine

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = render_demo_to_pixels(320, 240)
var visible: i32 = 0
for pixel in pixels:
    if pixel != 0xFFF0F0F0:
        visible = visible + 1
expect(visible).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/browser_demo_render_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser Demo rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
