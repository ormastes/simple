# gpu.engine2d.render.hud — HUD compositing unit specs

> Direct unit specs for `composite_hud`, extracted from Rollball's HUD overlay:

<!-- sdn-diagram:id=hud_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=hud_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

hud_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=hud_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gpu.engine2d.render.hud — HUD compositing unit specs

Direct unit specs for `composite_hud`, extracted from Rollball's HUD overlay:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Design | src/lib/nogc_async_mut/gpu/engine2d/render/hud.spl |
| Source | `test/01_unit/lib/nogc_async_mut/gpu/engine2d/render/hud_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Direct unit specs for `composite_hud`, extracted from Rollball's HUD overlay:
absolute pixel oracles on a small hand-constructed framebuffer.

## Scenarios

### gpu.engine2d.render.hud — composite_hud

#### overlays an opaque bg bar over the top rows and preserves pixels below it

- assert equal
- assert equal
- assert equal
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w: i32 = 40
val h: i32 = 30
val bg: u32 = 0xFF101018
val fg: u32 = 0xFFFFFFFF
val original: u32 = 0xFF203040
var px: [u32] = [original; 1200]
val out = composite_hud(px, w, h, "T", bg, fg)
assert_equal(out.len(), 1200)
# Bar pixel inside the 18-row bar, away from glyph ink.
assert_equal(out[2 * w + 30], bg)
# Below the bar the original pixel is preserved exactly.
assert_equal(out[20 * w + 5], original)
# At least one foreground (glyph) pixel was drawn somewhere in the bar.
var white: i64 = 0
var i: i64 = 0
while i < 18 * (w as i64):
    if out[i] == fg:
        white = white + 1
    i = i + 1
assert_true(white > 0)
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

- **Design:** [src/lib/nogc_async_mut/gpu/engine2d/render/hud.spl](src/lib/nogc_async_mut/gpu/engine2d/render/hud.spl)


</details>
