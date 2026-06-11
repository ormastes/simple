# Tmp Test73 Specification

> <details>

<!-- sdn-diagram:id=tmp_test73_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_test73_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_test73_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_test73_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Test73 Specification

## Scenarios

### BrowserRenderer HTML rendering

#### uses the same pixels as an explicit Engine2D software renderer

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 90px; height: 40px; background-color: #2050a0'></div><span style='color:#ffffff'>Hi</span></body></html>"
val default_renderer = BrowserRenderer.create(TEST_WIDTH, TEST_HEIGHT)
val software_renderer = BrowserRenderer.create_with_backend(TEST_WIDTH, TEST_HEIGHT, "software")
val default_pixels = default_renderer.render_html_to_pixels(html).pixel_data
val software_pixels = software_renderer.render_html_to_pixels(html).pixel_data
expect(default_renderer.engine.?).to_equal(false)
expect(software_renderer.engine.?).to_equal(true)
expect(default_renderer.backend_name()).to_equal("software")
expect(software_renderer.backend_name()).to_equal("software")
expect(_pixels_equal(default_pixels, software_pixels)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_test73_spec.spl` |
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
