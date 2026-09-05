# Engine2D Render Surface Matrix Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D Render Surface Matrix Specification

## Scenarios

### Engine2D rendering surface

#### reproduces exact pixels for one hundred real Engine2D frames

A real CPU Engine2D surface is cleared, receives a filled rectangle, presents,
and is read back on every frame. All twelve ARGB pixels must match the frozen
absolute oracle; the readback must remain a CPU-owned mirror with no backend
handle and a positive checksum.

<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render and read back the deterministic CPU surface")
val background = 0xff102030u32
val foreground = 0xffa0b0c0u32
val expected = [
    background, background, background, background,
    background, foreground, foreground, background,
    background, background, background, background
]
var engine = Engine2D.create_with_backend(4, 3, "cpu")
expect(engine.backend_name()).to_equal("cpu")
var frame = 0
while frame < 100:
    engine.clear(background)
    engine.draw_rect_filled(1, 1, 2, 1, foreground)
    engine.present()
    val readback = engine.read_pixels_with_source()
    expect(readback.pixels).to_equal(expected)
    expect(readback.source).to_equal("cpu_mirror")
    expect(readback.pixel_count).to_equal(12)
    expect(readback.backend_handle).to_equal(0)
    expect(readback.checksum).to_be_greater_than(0)
    frame = frame + 1
engine.shutdown()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Integration |
| Status | Active |
| Source | `test/02_integration/rendering/engine2d_render_surface_matrix_spec.spl` |
| Updated | 2026-07-27 |
| Generator | Manual synchronization while the self-hosted checker crash is open |

## Coverage Boundary

This scenario owns repeated-frame determinism and one frozen absolute surface
oracle. Existing real Engine2D specs own the broader primitive, effect,
resource, invalid-input, strict-backend, and device-readback matrices; this
manual does not duplicate or relabel those results.

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

</details>
