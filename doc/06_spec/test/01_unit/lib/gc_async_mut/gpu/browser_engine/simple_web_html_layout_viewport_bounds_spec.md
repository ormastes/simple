# Simple Web HTML Layout Viewport Bounds Spec

> The normal and scroll software-pixel entrypoints feed the shared Engine2D presentation path. They must fail closed for impossible or oversized viewport dimensions instead of allocating `width * height` pixels.

<!-- sdn-diagram:id=simple_web_html_layout_viewport_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_html_layout_viewport_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_html_layout_viewport_bounds_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_html_layout_viewport_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web HTML Layout Viewport Bounds Spec

The normal and scroll software-pixel entrypoints feed the shared Engine2D presentation path. They must fail closed for impossible or oversized viewport dimensions instead of allocating `width * height` pixels.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_viewport_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The normal and scroll software-pixel entrypoints feed the shared Engine2D
presentation path. They must fail closed for impossible or oversized viewport
dimensions instead of allocating `width * height` pixels.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec` and direct pixel-array length assertions.

## Scenarios

### SimpleWebHtmlLayoutViewportBounds

#### rejects non-positive and oversized viewport allocations

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<main><p>bounded</p></main>"

val zero_width = simple_web_layout_render_html_software_pixels(html, 0, 16)
expect(zero_width.len()).to_equal(0)

val negative_height = simple_web_layout_render_html_software_pixels(html, 16, -1)
expect(negative_height.len()).to_equal(0)

val oversized = simple_web_layout_render_html_software_pixels(html, 4097, 1025)
expect(oversized.len()).to_equal(0)

val oversized_scroll = simple_web_layout_render_html_software_pixels_at_scroll(html, 4097, 1025, 32)
expect(oversized_scroll.len()).to_equal(0)
```

</details>

#### rejects oversized scroll extents before virtual layout height expansion

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<main><p>bounded</p></main>"

val negative_scroll = simple_web_layout_render_html_software_pixels_at_scroll(html, 16, 16, -8)
expect(negative_scroll.len()).to_equal(256)

val oversized_scroll_extent = simple_web_layout_render_html_software_pixels_at_scroll(html, 16, 16, 4194304)
expect(oversized_scroll_extent.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [.spipe/web_rendering_backend_animation_hardening/state.md](.spipe/web_rendering_backend_animation_hardening/state.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
