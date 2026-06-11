# Browser Renderer Smoke Specification

> <details>

<!-- sdn-diagram:id=browser_renderer_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_renderer_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_renderer_smoke_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_renderer_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Smoke Specification

## Scenarios

### BrowserRenderer bounded smoke

#### renders inline background blocks without producing a blank frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body><div style='width: 120px; height: 60px; background-color: #ff0000'></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, SMOKE_WIDTH, SMOKE_HEIGHT).pixel_data
expect(pixels.len()).to_equal(SMOKE_WIDTH * SMOKE_HEIGHT)
expect(_count_non_background(pixels, WHITE_BG)).to_be_greater_than(0)
```

</details>

#### renders style block CSS into fallback pixels

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; } .card { width: 12px; height: 8px; background-color: #2563eb; }</style></head><body><div class='card'></div></body></html>"
val pixels = render_html_to_pixels_with_viewport(html, SMOKE_WIDTH, SMOKE_HEIGHT).pixel_data
expect(_count_color(pixels, 0xFF2563EBu32)).to_be_greater_than(0)
```

</details>

#### is deterministic for repeated renders of the same HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><body style='margin:0; background:#ffffff'><div style='width:10px; height:10px; background:#16a34a'></div></body></html>"
val first = render_html_to_pixels_with_viewport(html, SMOKE_WIDTH, SMOKE_HEIGHT).pixel_data
val second = render_html_to_pixels_with_viewport(html, SMOKE_WIDTH, SMOKE_HEIGHT).pixel_data
expect(_pixels_equal(first, second)).to_equal(true)
```

</details>

#### keeps explicit Engine2D software rendering available

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val renderer = create_software_browser_renderer(SMOKE_WIDTH, SMOKE_HEIGHT)
val result = renderer.render_html("<html><body><div style='width:10px; height:10px; background:#dc2626'></div></body></html>")
expect(result.width).to_equal(SMOKE_WIDTH)
expect(result.height).to_equal(SMOKE_HEIGHT)
expect(_count_color(result.pixel_data, 0xFFDC2626u32)).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BrowserRenderer bounded smoke

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
