# Tmp Tests73 Specification

> <details>

<!-- sdn-diagram:id=tmp_tests73_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tmp_tests73_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tmp_tests73_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tmp_tests73_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmp Tests73 Specification

## Scenarios

### tests 73-77

#### uses the same pixels as an explicit Engine2D software renderer

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 12px; height: 8px; background-color: #2563eb'></div></body></html>"
val viewport_pixels = render_html_to_pixels_with_viewport(html, TEST_WIDTH, TEST_HEIGHT).pixel_data
val explicit_renderer = create_software_browser_renderer(TEST_WIDTH, TEST_HEIGHT)
val explicit_pixels = explicit_renderer.render_html_to_pixels(html).pixel_data
expect(_pixels_equal(viewport_pixels, explicit_pixels)).to_equal(true)
```

</details>

#### reports deterministic software for unknown backend fallback

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 12px; height: 8px; background-color: #2563eb'></div></body></html>"
val renderer = BrowserRenderer.create_with_backend(TEST_WIDTH, TEST_HEIGHT, "unknown_xyz")
expect(renderer.backend_name()).to_equal("software")
```

</details>

#### module pixel helper matches explicit Engine2D software rendering

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 12px; height: 8px; background-color: #2563eb'></div></body></html>"
val helper_pixels = render_html_to_pixel_array(html, TEST_WIDTH, TEST_HEIGHT)
val explicit_renderer = create_software_browser_renderer(TEST_WIDTH, TEST_HEIGHT)
val explicit_pixels = explicit_renderer.render_html_to_pixels(html).pixel_data
expect(_pixels_equal(helper_pixels, explicit_pixels)).to_equal(true)
```

</details>

#### Engine2D bridge keeps explicit backend rendering available

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 12px; height: 8px; background-color: #2563eb'></div></body></html>"
val explicit_renderer = BrowserRenderer.create_with_backend(TEST_WIDTH, TEST_HEIGHT, "software")
val explicit_pixels = explicit_renderer.render_html_to_pixels(html).pixel_data
expect(_count_color(explicit_pixels, 0xFF2563EBu32)).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/tmp_tests73_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- tests 73-77

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
