# Wm Aetheric Web Material Specification

> <details>

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Aetheric Web Material Specification

## Scenarios

### Aetheric WM Web material adapter

#### preserves package glass through computed style and Draw IR

-  wm draw ir style value
-  wm draw ir style value
-  wm draw ir style value
-  wm draw ir style value
-  wm draw ir style value
-  wm draw ir style value
-  wm draw ir style value
   - Expected: layout.material_witness.cpu_composited_count equals `1`
   - Expected: layout.material_witness.cpu_composited_sha256.len() equals `64`
   - Expected: layout.material_fallback.kind equals `none`
   - Expected: execution.readback.pixels.len() equals `80 * 40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 57 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = simple_web_content_full_html_with_theme(
    "aetheric_dark", "Aetheric", "<p>content</p>", 80, 40
)
val layout = simple_web_layout_render_html_draw_ir_result(html, 80, 40)
val execution = simple_web_layout_render_html_readback_engine2d_result(
    html, 80, 40, "software"
)
expect(html).to_contain(
    "data-wm-theme-material-mode='engine2d-cpu-composited-material-v1'"
)
expect(layout.composition.batches.len()).to_be_greater_than(0)
val commands = layout.composition.batches[0].commands
expect(commands.len()).to_be_greater_than(0)
val content = _wm_draw_ir_command_by_id(commands, "wm-app-content")
expect(content.component_id).to_equal("wm-app-content")
expect(content.color).to_equal(0xFF1F1F21u32)
expect(
    _wm_draw_ir_style_value(content, "background-color")
).to_equal("3424591649")
expect(
    _wm_draw_ir_style_value(content, "background-image")
).to_equal("linear-gradient(352321535,117440511)")
expect(
    _wm_draw_ir_style_value(content, "background-layers-raw")
).to_equal("")
expect(
    _wm_draw_ir_style_value(content, "backdrop-filter")
).to_equal("blur(30px) saturate(170%)")
expect(
    _wm_draw_ir_style_value(content, "backdrop-filter-capability")
).to_equal("engine2d-cpu-composited-material-v1")
expect(
    _wm_draw_ir_style_value(content, "wm-material-request")
).to_equal("window-surface-glass")
expect(
    _wm_draw_ir_style_value(content, "backdrop-filter-realized")
).to_equal("blur(4px) saturate(170%)")
expect(
    _wm_draw_ir_style_value(
        content, "backdrop-filter-reduction-reason"
    )
).to_equal("cpu-blur-radius-bounded-to-4")
expect(
    _wm_draw_ir_style_value(
        content, "background-image-composite-mode"
    )
).to_equal("surface-then-alpha-gradient")
expect(layout.material_witness.cpu_composited_count).to_equal(1)
expect(layout.material_witness.cpu_composited_sha256.len()).to_equal(64)
expect(layout.material_fallback.kind).to_equal("none")
expect(execution.readback.pixels.len()).to_equal(80 * 40)
expect(execution.material_fallback.kind).to_equal(
    "cpu-composited-material"
)
expect(execution.material_fallback.material_sha256).to_equal(
    layout.material_witness.cpu_composited_sha256
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/compositor/wm_aetheric_web_material_spec.spl` |
| Updated | 2026-07-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Aetheric WM Web material adapter

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
