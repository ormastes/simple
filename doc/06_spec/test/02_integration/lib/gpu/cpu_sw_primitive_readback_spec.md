# CPU / Software Per-Primitive Framebuffer Readback

> The software backend is the only fully-honest 2D rasterizer, so it is the

<!-- sdn-diagram:id=cpu_sw_primitive_readback_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cpu_sw_primitive_readback_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cpu_sw_primitive_readback_spec -> std
cpu_sw_primitive_readback_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cpu_sw_primitive_readback_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CPU / Software Per-Primitive Framebuffer Readback

The software backend is the only fully-honest 2D rasterizer, so it is the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing \| **Status:** In Progress |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md |
| Design | N/A |
| Research | N/A |
| Source | `test/02_integration/lib/gpu/cpu_sw_primitive_readback_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

The software backend is the only fully-honest 2D rasterizer, so it is the
absolute drawing oracle that runs on any host. For each primitive we draw onto
a blank framebuffer, download the pixels with `read_pixels()`, and assert two
absolute facts: a known drawn point equals the draw color, and a known
background point stays opaque black. Comparing all four ARGB channels means a
no-op backend (which would leave the whole buffer black) can never pass.

## Scenarios

### software backend per-primitive readback

#### fills a rectangle and reads the interior as the draw color

- Draw a filled rectangle and read the framebuffer back
- assert primitive readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Draw a filled rectangle and read the framebuffer back")
assert_primitive_readback("fill_rect")
```

</details>

#### strokes a rectangle outline leaving the interior as background

- Draw a rectangle outline and read the framebuffer back
- assert primitive readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Draw a rectangle outline and read the framebuffer back")
assert_primitive_readback("stroke_rect")
```

</details>

#### draws a horizontal line and reads the line pixel as the draw color

- Draw a line and read the framebuffer back
- assert primitive readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Draw a line and read the framebuffer back")
assert_primitive_readback("line")
```

</details>

#### fills a circle and reads the disk center as the draw color

- Draw a filled circle and read the framebuffer back
- assert primitive readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Draw a filled circle and read the framebuffer back")
assert_primitive_readback("circle_filled")
```

</details>

#### strokes a circle outline leaving the ring center as background

- Draw a circle outline and read the framebuffer back
- assert primitive readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Draw a circle outline and read the framebuffer back")
assert_primitive_readback("circle_outline")
```

</details>

#### fills a rounded rectangle and reads the interior as the draw color

- Draw a filled rounded rectangle and read the framebuffer back
- assert primitive readback


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Draw a filled rounded rectangle and read the framebuffer back")
assert_primitive_readback("rounded_rect")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md](doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md)


</details>
