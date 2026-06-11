# Tmp Test77 Specification

> <details>

<!-- sdn-diagram:id=tmp_test77_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_test77_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_test77_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_test77_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Test77 Specification

## Scenarios

### BrowserRenderer HTML rendering

#### Engine2D bridge keeps explicit backend rendering available

- bridge renderer render html to pixels
- explicit renderer render html to pixels


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 70px; height: 24px; background-color: #4488cc'></div></body></html>"
val bridge_renderer = create_software_browser_renderer(TEST_WIDTH, TEST_HEIGHT)
val explicit_renderer = create_gpu_browser_renderer_with_backend(TEST_WIDTH, TEST_HEIGHT, "software")
expect(bridge_renderer.engine.?).to_equal(true)
expect(explicit_renderer.engine.?).to_equal(true)
expect(_pixels_equal(
    bridge_renderer.render_html_to_pixels(html).pixel_data,
    explicit_renderer.render_html_to_pixels(html).pixel_data
)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_test77_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserRenderer HTML rendering

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
