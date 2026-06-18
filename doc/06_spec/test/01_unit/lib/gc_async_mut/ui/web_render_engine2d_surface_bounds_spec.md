# Web-Render Engine2D Surface Bounds Spec

> The shared web-render backend path can be driven by browser, JavaScript, WASM, Simple2D, and animation surfaces. This spec keeps an oversized surface request from reaching backend framebuffer allocation.

<!-- sdn-diagram:id=web_render_engine2d_surface_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_render_engine2d_surface_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_render_engine2d_surface_bounds_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_render_engine2d_surface_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web-Render Engine2D Surface Bounds Spec

The shared web-render backend path can be driven by browser, JavaScript, WASM, Simple2D, and animation surfaces. This spec keeps an oversized surface request from reaching backend framebuffer allocation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/gc_async_mut/ui/web_render_engine2d_surface_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The shared web-render backend path can be driven by browser, JavaScript, WASM,
Simple2D, and animation surfaces. This spec keeps an oversized surface request
from reaching backend framebuffer allocation.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec` scenarios and direct value assertions.

## Scenarios

### web-render Engine2D surface bounds hardening

#### rejects oversized web surfaces before backend framebuffer allocation

- Request a surface one pixel above the shared Engine2D allocation cap
- Assert the request fails closed without pixels or backend provenance
   - Expected: s.rendered is false
   - Expected: s.pixels.len() equals `0`
   - Expected: s.backend_name equals ``
   - Expected: s.width equals `4096`
   - Expected: s.height equals `4097`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Request a surface one pixel above the shared Engine2D allocation cap")
val html = "<html><body style='background:#224466'><main><p>web</p></main></body></html>"
val s = web_render_html_via_engine2d(html, 4096, 4097, "vulkan")

step("Assert the request fails closed without pixels or backend provenance")
expect(s.rendered).to_equal(false)
expect(s.pixels.len()).to_equal(0)
expect(s.backend_name).to_equal("")
expect(s.width).to_equal(4096)
expect(s.height).to_equal(4097)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [.spipe/web_rendering_backend_animation_hardening/state.md](.spipe/web_rendering_backend_animation_hardening/state.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
