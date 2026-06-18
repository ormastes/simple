# Simple Web HTML Engine2D Presenter Bounds Spec

> The HTML layout renderer fails closed for invalid or oversized viewports by returning an empty pixel buffer. The presenter must preserve that rejection and avoid creating a GPU/Engine2D backend with the rejected dimensions.

<!-- sdn-diagram:id=simple_web_html_engine2d_presenter_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_html_engine2d_presenter_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_html_engine2d_presenter_bounds_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_html_engine2d_presenter_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web HTML Engine2D Presenter Bounds Spec

The HTML layout renderer fails closed for invalid or oversized viewports by returning an empty pixel buffer. The presenter must preserve that rejection and avoid creating a GPU/Engine2D backend with the rejected dimensions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_html_engine2d_presenter_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The HTML layout renderer fails closed for invalid or oversized viewports by
returning an empty pixel buffer. The presenter must preserve that rejection and
avoid creating a GPU/Engine2D backend with the rejected dimensions.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec` and direct readback metadata assertions.

## Scenarios

### SimpleWebHtmlEngine2dPresenterBounds

#### does not request Engine2D when layout viewport allocation is rejected

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val readback = simple_web_layout_render_html_readback("<main><p>oversized</p></main>", 4097, 1025, "vulkan")

expect(readback.source).to_equal("not_requested")
expect(readback.pixel_count).to_equal(0)
expect(readback.backend_handle).to_equal(0)
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
