# Simple Web Html Renderer Specification

> <details>

<!-- sdn-diagram:id=simple_web_html_renderer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_html_renderer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_html_renderer_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_html_renderer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Html Renderer Specification

## Scenarios

### SimpleWebHtmlRenderer

#### renders a white framebuffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pixels = simple_web_render_html_to_pixels("<html></html>", 4, 3)
expect(pixels.len()).to_equal(12)
expect(pixels[0]).to_equal(0xFFFFFFFFu32)
expect(pixels[11]).to_equal(0xFFFFFFFFu32)
```

</details>

#### reuses retained pixels for unchanged html

1. var cache = SimpleWebHtmlPixelCache create
   - Expected: first.len() equals `12`
   - Expected: second.len() equals `12`
   - Expected: cache.stores equals `1`
   - Expected: cache.hits equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cache = SimpleWebHtmlPixelCache.create(4, 3)
val first = cache.pixels_for_html("<html></html>")
val second = cache.pixels_for_html("<html></html>")
expect(first.len()).to_equal(12)
expect(second.len()).to_equal(12)
expect(cache.stores).to_equal(1)
expect(cache.hits).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_renderer_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleWebHtmlRenderer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
