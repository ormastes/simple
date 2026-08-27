# Window Scene Draw Ir Specification

> Tests covering window scene Draw IR projection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Window Scene Draw Ir Specification

## Scenarios

### window scene Draw IR projection

#### retains readable bitmap text when selected metrics are unavailable

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- retains readable bitmap text when selected metrics are unavailable
   - Expected: fallback.kind equals `DRAW_IR_COMMAND_TEXT`
   - Expected: fallback.computed_style.len() equals `0`
   - Expected: source does not contain `draw_ir_rect(component_id, x, legacy_y, bar_w, 2, color)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("retains readable bitmap text when selected metrics are unavailable")
val source = rt_file_read_text("src/lib/common/ui/window_scene_draw_ir.spl")
val draw_ir_route = rt_file_read_text("src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl")
val engine = rt_file_read_text("src/lib/gc_async_mut/gpu/engine2d/engine.spl")
val baremetal = rt_file_read_text("src/lib/gc_async_mut/gpu/engine2d/backend_baremetal.spl")
val fallback = draw_ir_text("fallback", 1, 2, "A", 0xffffffffu32)
expect(fallback.kind).to_equal(DRAW_IR_COMMAND_TEXT)
expect(fallback.computed_style.len()).to_equal(0)
expect(source).to_contain("draw_ir_text(component_id, x, legacy_y, value, color)")
expect(source.contains("draw_ir_rect(component_id, x, legacy_y, bar_w, 2, color)")).to_equal(false)
expect(draw_ir_route).to_contain("if font_identity != \"\":")
expect(draw_ir_route).to_contain("eng.draw_text(x, y, command.text_value, command.color")
expect(engine).to_contain("if selected != nil:")
expect(engine).to_contain("bm.draw_text(x, y, text_val, color, font_size)")
expect(baremetal).to_contain("render_text_to_buffer(buf, text_w, text_h, 0, 0, text_val, color, font_size)")
```

</details>

#### projects the window manager chrome and windows into composed Draw IR batches

- projects the window manager chrome and windows into composed Draw IR batches
   - Expected: composition.composition_id equals `wm-composite`
   - Expected: composition.scene_key equals `shared_wm_scene_layout_key(scene)`
   - Expected: composition.backend_target equals `DRAW_IR_BACKEND_GPU`
   - Expected: composition.batches.len() equals `5`
   - Expected: composition.batches[0].embedding.component_id equals `desktop`
   - Expected: composition.batches[1].embedding.component_id equals `wm-chrome`
   - Expected: composition.batches[2].embedding.surface_id equals `surf1`
   - Expected: composition.batches[3].embedding.surface_id equals `surf2`
   - Expected: composition.batches[4].embedding.component_id equals `wm-taskbar-objects`
   - Expected: clock.component_id equals `taskbar-clock`
   - Expected: clock.kind equals `DRAW_IR_COMMAND_TEXT`
   - Expected: clock.text_value equals `09:41`
   - Expected: clock.computed_style[0].value equals `Noto Sans Mono`
   - Expected: clock.computed_style[3].value equals `12`
   - Expected: composition.batches[0].source.source_kind equals `DRAW_IR_SOURCE_WM_SCENE`
   - Expected: composition.batches[1].source.source_id equals `wm.chrome`
   - Expected: composition.batches[2].source.source_id equals `wm.window.win1`
   - Expected: composition.batches[2].source.style_key equals `wm.window`
   - Expected: composition.batches[2].embedding.x equals `10`
   - Expected: composition.batches[2].embedding.y equals `40`
   - Expected: composition.batches[2].embedding.width equals `305`
   - Expected: composition.batches[2].embedding.height equals `206`
   - Expected: composition.batches[3].embedding.x equals `80`
   - Expected: composition.batches[3].embedding.y equals `120`
   - Expected: composition.batches[3].commands[0].kind equals `DRAW_IR_COMMAND_RECT`
   - Expected: composition.batches[3].commands[6].kind equals `DRAW_IR_COMMAND_TEXT`
   - Expected: title.computed_style[0].value equals `Noto Sans Mono`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("projects the window manager chrome and windows into composed Draw IR batches")
val scene = _scene()
val composition = shared_wm_scene_draw_ir_composition(scene, _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)

expect(composition.composition_id).to_equal("wm-composite")
expect(composition.scene_key).to_equal(shared_wm_scene_layout_key(scene))
expect(composition.backend_target).to_equal(DRAW_IR_BACKEND_GPU)
expect(composition.batches.len()).to_equal(5)
expect(composition.batches[0].embedding.component_id).to_equal("desktop")
expect(composition.batches[1].embedding.component_id).to_equal("wm-chrome")
expect(composition.batches[2].embedding.surface_id).to_equal("surf1")
expect(composition.batches[3].embedding.surface_id).to_equal("surf2")
expect(composition.batches[4].embedding.component_id).to_equal("wm-taskbar-objects")
val clock = composition.batches[4].commands[10]
expect(clock.component_id).to_equal("taskbar-clock")
expect(clock.kind).to_equal(DRAW_IR_COMMAND_TEXT)
expect(clock.text_value).to_equal("09:41")
expect(clock.computed_style.len()).to_be_greater_than(3)
expect(clock.computed_style[0].value).to_equal("Noto Sans Mono")
expect(clock.computed_style[1].value).to_start_with("sha256=")
expect(clock.computed_style[3].value).to_equal("12")
expect(composition.batches[0].source.source_kind).to_equal(DRAW_IR_SOURCE_WM_SCENE)
expect(composition.batches[1].source.source_id).to_equal("wm.chrome")
expect(composition.batches[2].source.source_id).to_equal("wm.window.win1")
expect(composition.batches[2].source.style_key).to_equal("wm.window")
expect(composition.batches[2].source.style_revision).to_contain("xy=10,40")
expect(composition.batches[2].source.style_revision).to_contain("size=300x200")
expect(composition.batches[2].embedding.x).to_equal(10)
expect(composition.batches[2].embedding.y).to_equal(40)
expect(composition.batches[2].embedding.width).to_equal(305)
expect(composition.batches[2].embedding.height).to_equal(206)
expect(composition.batches[3].embedding.x).to_equal(80)
expect(composition.batches[3].embedding.y).to_equal(120)
expect(composition.batches[3].commands[0].kind).to_equal(DRAW_IR_COMMAND_RECT)
expect(composition.batches[3].commands[6].kind).to_equal(DRAW_IR_COMMAND_TEXT)
val title = composition.batches[3].commands[6]
if title.computed_style.len() > 0:
    expect(title.computed_style[0].value).to_equal("Noto Sans Mono")
    expect(title.computed_style[1].value).to_start_with("sha256=")
    expect(title.computed_style[2].value).to_contain(",")
    expect(title.width).to_be_greater_than(0)
```

</details>

#### keeps Draw IR source revisions stable for unchanged scenes

- keeps Draw IR source revisions stable for unchanged scenes
   - Expected: second.batches[0].source.style_revision equals `first.batches[0].source.style_revision`
   - Expected: second.batches[1].source.style_revision equals `first.batches[1].source.style_revision`
   - Expected: second.batches[2].source.style_revision equals `first.batches[2].source.style_revision`
   - Expected: second.batches[3].source.style_revision equals `first.batches[3].source.style_revision`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps Draw IR source revisions stable for unchanged scenes")
val scene = _scene()
val first = shared_wm_scene_draw_ir_composition(scene, _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)
val second = shared_wm_scene_draw_ir_composition(scene, _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)

expect(second.batches[0].source.style_revision).to_equal(first.batches[0].source.style_revision)
expect(second.batches[1].source.style_revision).to_equal(first.batches[1].source.style_revision)
expect(second.batches[2].source.style_revision).to_equal(first.batches[2].source.style_revision)
expect(second.batches[3].source.style_revision).to_equal(first.batches[3].source.style_revision)
```

</details>

#### keeps the no-snapshot WM Draw IR stream byte-compatible with legacy rectangles

- keeps the no-snapshot WM Draw IR stream byte-compatible with legacy rectangles
   - Expected: window_batch.commands.len() equals `9`
   - Expected: shadow.component_id equals `win2-shadow`
   - Expected: shadow.kind equals `DRAW_IR_COMMAND_RECT`
   - Expected: shadow.color equals `theme.window_shadow`
   - Expected: shadow.computed_style.len() equals `0`
   - Expected: shadow.hit_rect.present is false
   - Expected: body.component_id equals `win2-body`
   - Expected: body.kind equals `DRAW_IR_COMMAND_RECT`
   - Expected: body.color equals `theme.host_window_body`
   - Expected: body.width equals `300`
   - Expected: body.height equals `200`
   - Expected: body.computed_style.len() equals `0`
   - Expected: body.hit_rect.present is false
   - Expected: body.clip_rect.present is false
   - Expected: titlebar.component_id equals `win2-titlebar`
   - Expected: titlebar.kind equals `DRAW_IR_COMMAND_RECT`
   - Expected: titlebar.color equals `theme.title_unfocused`
   - Expected: titlebar.height equals `28`
   - Expected: titlebar.computed_style.len() equals `0`
   - Expected: window_batch.commands[3].component_id equals `win2-traffic-red`
   - Expected: window_batch.commands[3].color equals `0xFFE74C3Cu32`
   - Expected: window_batch.commands[4].component_id equals `win2-traffic-yellow`
   - Expected: window_batch.commands[4].color equals `0xFFF1C40Fu32`
   - Expected: window_batch.commands[5].component_id equals `win2-traffic-green`
   - Expected: window_batch.commands[5].color equals `0xFF27AE60u32`
   - Expected: window_batch.commands[6].component_id equals `win2-title`
   - Expected: window_batch.commands[6].text_value equals `Window Two`
   - Expected: window_batch.commands[6].x equals `66`
   - Expected: window_batch.commands[7].component_id equals `win2-close`
   - Expected: window_batch.commands[7].color equals `theme.close_button`
   - Expected: window_batch.commands[8].component_id equals `win2-close-label`
   - Expected: window_batch.commands[8].text_value equals `X`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps the no-snapshot WM Draw IR stream byte-compatible with legacy rectangles")
reset_wm_chrome_theme()
val composition = shared_wm_scene_draw_ir_composition(_scene(), _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)
val window_batch = composition.batches[3]
val shadow = window_batch.commands[0]
val body = window_batch.commands[1]
val titlebar = window_batch.commands[2]
val theme = wm_chrome_theme()

expect(window_batch.commands.len()).to_equal(9)
expect(shadow.component_id).to_equal("win2-shadow")
expect(shadow.kind).to_equal(DRAW_IR_COMMAND_RECT)
expect(shadow.color).to_equal(theme.window_shadow)
expect(shadow.computed_style.len()).to_equal(0)
expect(shadow.hit_rect.present).to_equal(false)
expect(body.component_id).to_equal("win2-body")
expect(body.kind).to_equal(DRAW_IR_COMMAND_RECT)
expect(body.color).to_equal(theme.host_window_body)
expect(body.width).to_equal(300)
expect(body.height).to_equal(200)
expect(body.computed_style.len()).to_equal(0)
expect(body.hit_rect.present).to_equal(false)
expect(body.clip_rect.present).to_equal(false)
expect(titlebar.component_id).to_equal("win2-titlebar")
expect(titlebar.kind).to_equal(DRAW_IR_COMMAND_RECT)
expect(titlebar.color).to_equal(theme.title_unfocused)
expect(titlebar.height).to_equal(28)
expect(titlebar.computed_style.len()).to_equal(0)
expect(window_batch.commands[3].component_id).to_equal("win2-traffic-red")
expect(window_batch.commands[3].color).to_equal(0xFFE74C3Cu32)
expect(window_batch.commands[4].component_id).to_equal("win2-traffic-yellow")
expect(window_batch.commands[4].color).to_equal(0xFFF1C40Fu32)
expect(window_batch.commands[5].component_id).to_equal("win2-traffic-green")
expect(window_batch.commands[5].color).to_equal(0xFF27AE60u32)
expect(window_batch.commands[6].component_id).to_equal("win2-title")
expect(window_batch.commands[6].text_value).to_equal("Window Two")
expect(window_batch.commands[6].x).to_equal(66)
expect(window_batch.commands[7].component_id).to_equal("win2-close")
expect(window_batch.commands[7].color).to_equal(theme.close_button)
expect(window_batch.commands[8].component_id).to_equal("win2-close-label")
expect(window_batch.commands[8].text_value).to_equal("X")
```

</details>

#### requests Metal device glass with canonical body and title material semantics

- requests Metal device glass with canonical body and title material semantics
   - Expected: composition.batches[3].commands.len() equals `8`
   - Expected: composition.backend_target equals `metal`
   - Expected: focused_body.component_id equals `win2-body`
   - Expected: focused_body.color equals `snapshot.material.window_fill_rgba`
   - Expected: _style_value(focused_body, "background-color") equals `snapshot.material.window_fill_rgba.to_string()`
   - Expected: _style_value(focused_body, "wm-theme-id") equals `snapshot.id`
   - Expected: _style_value(focused_body, "wm-theme-family-id") equals `snapshot.family_id`
   - Expected: _style_value(focused_body, "wm-theme-source-reference") equals `snapshot.source_reference`
   - Expected: _style_value(focused_body, "wm-theme-source-manifest-sha256") equals `snapshot.source_manifest_sha256`
   - Expected: _style_value(focused_body, "wm-theme-material-sha256") equals `snapshot.material_sha256`
   - Expected: snapshot.material.window_gradient_start_rgba equals `352321535u32`
   - Expected: snapshot.material.window_gradient_end_rgba equals `117440511u32`
   - Expected: _style_value(focused_body, "background-image") equals `linear-gradient(352321535,117440511)`
   - Expected: _style_value(focused_body, "background-image-capability") equals `engine2d-rounded-material-v1`
   - Expected: _style_value(focused_body, "background-image-source-css") equals `snapshot.material.window_gradient_source_css`
   - Expected: _style_value(focused_body, "background-image-composite-mode") equals `surface-then-alpha-gradient`
   - Expected: _style_value(focused_body, "background-image-fallback") equals ``
   - Expected: _style_value(focused_body, "background-image-fallback-reason") equals ``
   - Expected: _style_value(focused_body, "border-radius") equals `18`
   - Expected: _style_value(focused_body, "box-shadow-raw") equals `0px 28px 76px 0px 1962934272`
   - Expected: _style_value(focused_body, "box-shadow") equals `0px 28px 1962934272`
   - Expected: _style_value(focused_body, "backdrop-filter") equals `blur(30px) saturate(170%)`
   - Expected: _style_value(focused_body, "backdrop-filter-capability") equals `engine2d-composited-glass-material-v1`
   - Expected: _style_value(focused_body, "backdrop-filter-requested-target") equals `metal-device-glass-v1`
   - Expected: _style_value(focused_body, "backdrop-filter-realized") equals `blur(4px) saturate(170%)`
   - Expected: _style_value(focused_body, "backdrop-filter-realized-blur-radius-px") equals `4`
   - Expected: _style_value(focused_body, "backdrop-filter-realized-saturation-milli") equals `1700`
   - Expected: _style_value(focused_body, "backdrop-filter-reduction-reason") equals `cpu-blur-radius-bounded-to-4`
   - Expected: _style_value(focused_body, "backdrop-filter-fallback") equals `cpu-composited-material`
   - Expected: _style_value(focused_body, "backdrop-filter-fallback-target") equals `cpu-scalar-glass-v1`
   - Expected: _style_value(focused_body, "backdrop-filter-fallback-reason") equals `metal-device-dispatch-unavailable-at-execution`
   - Expected: _style_value(focused_body, "wm-material-surface-alpha-milli") equals `800`
   - Expected: focused_title.color equals `snapshot.material.active_title_fill_rgba`
   - Expected: _style_value(focused_title, "background-color") equals `snapshot.material.active_title_fill_rgba.to_string()`
   - Expected: _style_value(focused_title, "background-image") equals `none`
   - Expected: _style_value(focused_title, "background-image-capability") equals `not-requested`
   - Expected: _style_value(focused_title, "background-image-fallback") equals ``
   - Expected: _style_value(focused_title, "backdrop-filter") equals `blur(30px) saturate(170%)`
   - Expected: _style_value(focused_title, "backdrop-filter-capability") equals `engine2d-composited-glass-material-v1`
   - Expected: _style_value(focused_title, "backdrop-filter-realized") equals `blur(4px) saturate(170%)`
   - Expected: _style_value(focused_title, "wm-material-surface-alpha-milli") equals `878`
   - Expected: inactive_body.color equals `snapshot.material.window_fill_rgba`
   - Expected: inactive_title.color equals `snapshot.material.inactive_title_fill_rgba`
   - Expected: _style_value(inactive_title, "wm-material-surface-alpha-milli") equals `800`
   - Expected: _style_value(inactive_body, "box-shadow-raw") equals `0px 18px 46px 0px 1459617792`
   - Expected: _style_value(focused_title, "font-family") equals `snapshot.material.font_family`
   - Expected: _style_value(title_text, "font-size") equals `14`
   - Expected: _style_value(title_text, "font-family-requested") equals `snapshot.material.font_family`
   - Expected: _style_value(title_text, "font-weight") equals `400`
   - Expected: _style_value(title_text, "color") equals `snapshot.material.text_rgba.to_string()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 64 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requests Metal device glass with canonical body and title material semantics")
val snapshot = aetheric_dark_theme_render_snapshot()
apply_theme_render_snapshot_to_wm_chrome(snapshot)
val composition = shared_wm_scene_draw_ir_composition(_scene(), _taskbar(), "metal", 1000, "09:41", 2)
val inactive_body = composition.batches[2].commands[0]
val inactive_title = composition.batches[2].commands[1]
val focused_body = composition.batches[3].commands[0]
val focused_title = composition.batches[3].commands[1]
val title_text = composition.batches[3].commands[5]

expect(composition.batches[3].commands.len()).to_equal(8)
expect(composition.backend_target).to_equal("metal")
expect(focused_body.component_id).to_equal("win2-body")
expect(focused_body.color).to_equal(snapshot.material.window_fill_rgba)
expect(_style_value(focused_body, "background-color")).to_equal(snapshot.material.window_fill_rgba.to_string())
expect(_style_value(focused_body, "wm-theme-id")).to_equal(snapshot.id)
expect(_style_value(focused_body, "wm-theme-family-id")).to_equal(snapshot.family_id)
expect(_style_value(focused_body, "wm-theme-source-reference")).to_equal(snapshot.source_reference)
expect(_style_value(focused_body, "wm-theme-source-manifest-sha256")).to_equal(snapshot.source_manifest_sha256)
expect(_style_value(focused_body, "wm-theme-material-sha256")).to_equal(snapshot.material_sha256)
expect(snapshot.material.window_gradient_available).to_be(true)
expect(snapshot.material.window_gradient_start_rgba).to_equal(352321535u32)
expect(snapshot.material.window_gradient_end_rgba).to_equal(117440511u32)
expect(_style_value(focused_body, "background-image")).to_equal("linear-gradient(352321535,117440511)")
expect(_style_value(focused_body, "background-image-capability")).to_equal("engine2d-rounded-material-v1")
expect(_style_value(focused_body, "background-image-source-css")).to_equal(snapshot.material.window_gradient_source_css)
expect(_style_value(focused_body, "background-image-composite-mode")).to_equal("surface-then-alpha-gradient")
expect(_style_value(focused_body, "background-image-fallback")).to_equal("")
expect(_style_value(focused_body, "background-image-fallback-reason")).to_equal("")
expect(_style_value(focused_body, "border-radius")).to_equal("18")
expect(_style_value(focused_body, "box-shadow-raw")).to_equal("0px 28px 76px 0px 1962934272")
expect(_style_value(focused_body, "box-shadow")).to_equal("0px 28px 1962934272")
expect(_style_value(focused_body, "backdrop-filter")).to_equal("blur(30px) saturate(170%)")
expect(_style_value(focused_body, "backdrop-filter-capability")).to_equal("engine2d-composited-glass-material-v1")
expect(_style_value(focused_body, "backdrop-filter-requested-target")).to_equal("metal-device-glass-v1")
expect(_style_value(focused_body, "backdrop-filter-realized")).to_equal("blur(4px) saturate(170%)")
expect(_style_value(focused_body, "backdrop-filter-realized-blur-radius-px")).to_equal("4")
expect(_style_value(focused_body, "backdrop-filter-realized-saturation-milli")).to_equal("1700")
expect(_style_value(focused_body, "backdrop-filter-reduction-reason")).to_equal("cpu-blur-radius-bounded-to-4")
expect(_style_value(focused_body, "backdrop-filter-fallback")).to_equal("cpu-composited-material")
expect(_style_value(focused_body, "backdrop-filter-fallback-target")).to_equal("cpu-scalar-glass-v1")
expect(_style_value(focused_body, "backdrop-filter-fallback-reason")).to_equal("metal-device-dispatch-unavailable-at-execution")
expect(_style_value(focused_body, "wm-material-surface-alpha-milli")).to_equal("800")
expect(focused_title.color).to_equal(snapshot.material.active_title_fill_rgba)
expect(_style_value(focused_title, "background-color")).to_equal(snapshot.material.active_title_fill_rgba.to_string())
expect(_style_value(focused_title, "background-image")).to_equal("none")
expect(_style_value(focused_title, "background-image-capability")).to_equal("not-requested")
expect(_style_value(focused_title, "background-image-fallback")).to_equal("")
expect(_style_value(focused_title, "backdrop-filter")).to_equal("blur(30px) saturate(170%)")
expect(_style_value(focused_title, "backdrop-filter-capability")).to_equal("engine2d-composited-glass-material-v1")
expect(_style_value(focused_title, "backdrop-filter-realized")).to_equal("blur(4px) saturate(170%)")
expect(_style_value(focused_title, "wm-material-surface-alpha-milli")).to_equal("878")
expect(inactive_body.color).to_equal(snapshot.material.window_fill_rgba)
expect(inactive_title.color).to_equal(snapshot.material.inactive_title_fill_rgba)
expect(_style_value(inactive_title, "wm-material-surface-alpha-milli")).to_equal("800")
expect(_style_value(inactive_body, "box-shadow-raw")).to_equal("0px 18px 46px 0px 1459617792")
expect(_style_value(focused_title, "font-family")).to_equal(snapshot.material.font_family)
expect(_style_value(title_text, "font-size")).to_equal("14")
expect(_style_value(title_text, "font-family-requested")).to_equal(snapshot.material.font_family)
expect(_style_value(title_text, "font-weight")).to_equal("400")
expect(_style_value(title_text, "color")).to_equal(snapshot.material.text_rgba.to_string())
expect(composition.batches[3].source.style_revision).to_contain(snapshot.material_sha256)
reset_wm_chrome_theme()
```

</details>

#### requests honest CPU-composited glass for canonical CPU software SIMD and Vulkan targets

- requests honest CPU-composited glass for canonical CPU software SIMD and Vulkan targets
   - Expected: cpu_composition.backend_target equals `DRAW_IR_BACKEND_CPU`
   - Expected: software_composition.backend_target equals `software`
   - Expected: simd_composition.backend_target equals `cpu_simd`
   - Expected: vulkan_composition.backend_target equals `vulkan`
   - Expected: body.color equals `0xFF1F1F21u32`
   - Expected: _style_value(body, "background-color") equals `snapshot.material.window_fill_rgba.to_string()`
   - Expected: _style_value(body, "background-image") equals `linear-gradient(352321535,117440511)`
   - Expected: _style_value(body, "background-image-capability") equals `engine2d-rounded-material-v1`
   - Expected: _style_value(body, "background-image-composite-mode") equals `surface-then-alpha-gradient`
   - Expected: _style_value(body, "backdrop-filter-capability") equals `engine2d-cpu-composited-material-v1`
   - Expected: _style_value(body, "backdrop-filter-requested-target") equals `cpu-scalar-glass-v1`
   - Expected: _style_value(body, "backdrop-filter-fallback-reason") equals `native-device-backdrop-path-pending`
   - Expected: _style_value(body, "backdrop-filter-realized") equals `blur(4px) saturate(170%)`
   - Expected: _style_value(body, "backdrop-filter-realized-blur-radius-px") equals `4`
   - Expected: _style_value(body, "backdrop-filter-realized-saturation-milli") equals `1700`
   - Expected: _style_value(body, "backdrop-filter-reduction-reason") equals `cpu-blur-radius-bounded-to-4`
   - Expected: _style_value(body, "wm-material-surface-alpha-milli") equals `800`
   - Expected: title.color equals `0xFF000000u32 | (snapshot.material.active_title_fill_rgba & 0x00FFFFFFu32)`
   - Expected: _style_value(title, "background-color") equals `snapshot.material.active_title_fill_rgba.to_string()`
   - Expected: _style_value(title, "background-image") equals `none`
   - Expected: _style_value(title, "background-image-capability") equals `not-requested`
   - Expected: _style_value(title, "backdrop-filter-capability") equals `engine2d-cpu-composited-material-v1`
   - Expected: _style_value(title, "backdrop-filter-requested-target") equals `cpu-scalar-glass-v1`
   - Expected: _style_value(title, "backdrop-filter-fallback-reason") equals `native-device-backdrop-path-pending`
   - Expected: _style_value(title, "backdrop-filter-realized") equals `blur(4px) saturate(170%)`
   - Expected: _style_value(title, "wm-material-surface-alpha-milli") equals `878`


<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requests honest CPU-composited glass for canonical CPU software SIMD and Vulkan targets")
val snapshot = _translucent_fallback_snapshot()
apply_theme_render_snapshot_to_wm_chrome(snapshot)
val cpu_composition = shared_wm_scene_draw_ir_composition(_scene(), _taskbar(), DRAW_IR_BACKEND_CPU, 1000, "09:41", 2)
val software_composition = shared_wm_scene_draw_ir_composition(_scene(), _taskbar(), "software", 1000, "09:41", 2)
val simd_composition = shared_wm_scene_draw_ir_composition(_scene(), _taskbar(), "cpu_simd", 1000, "09:41", 2)
val vulkan_composition = shared_wm_scene_draw_ir_composition(_scene(), _taskbar(), "vulkan", 1000, "09:41", 2)

expect(cpu_composition.backend_target).to_equal(DRAW_IR_BACKEND_CPU)
expect(software_composition.backend_target).to_equal("software")
expect(simd_composition.backend_target).to_equal("cpu_simd")
expect(vulkan_composition.backend_target).to_equal("vulkan")
for composition in [cpu_composition, software_composition, simd_composition, vulkan_composition]:
    val body = composition.batches[3].commands[0]
    val title = composition.batches[3].commands[1]
    expect(body.color).to_equal(0xFF1F1F21u32)
    expect(_style_value(body, "background-color")).to_equal(snapshot.material.window_fill_rgba.to_string())
    expect(_style_value(body, "background-image")).to_equal("linear-gradient(352321535,117440511)")
    expect(_style_value(body, "background-image-capability")).to_equal("engine2d-rounded-material-v1")
    expect(_style_value(body, "background-image-composite-mode")).to_equal("surface-then-alpha-gradient")
    expect(_style_value(body, "backdrop-filter-capability")).to_equal("engine2d-cpu-composited-material-v1")
    expect(_style_value(body, "backdrop-filter-requested-target")).to_equal("cpu-scalar-glass-v1")
    expect(_style_value(body, "backdrop-filter-fallback-reason")).to_equal("native-device-backdrop-path-pending")
    expect(_style_value(body, "backdrop-filter-realized")).to_equal("blur(4px) saturate(170%)")
    expect(_style_value(body, "backdrop-filter-realized-blur-radius-px")).to_equal("4")
    expect(_style_value(body, "backdrop-filter-realized-saturation-milli")).to_equal("1700")
    expect(_style_value(body, "backdrop-filter-reduction-reason")).to_equal("cpu-blur-radius-bounded-to-4")
    expect(_style_value(body, "wm-material-surface-alpha-milli")).to_equal("800")
    expect(title.color).to_equal(0xFF000000u32 | (snapshot.material.active_title_fill_rgba & 0x00FFFFFFu32))
    expect(_style_value(title, "background-color")).to_equal(snapshot.material.active_title_fill_rgba.to_string())
    expect(_style_value(title, "background-image")).to_equal("none")
    expect(_style_value(title, "background-image-capability")).to_equal("not-requested")
    expect(_style_value(title, "backdrop-filter-capability")).to_equal("engine2d-cpu-composited-material-v1")
    expect(_style_value(title, "backdrop-filter-requested-target")).to_equal("cpu-scalar-glass-v1")
    expect(_style_value(title, "backdrop-filter-fallback-reason")).to_equal("native-device-backdrop-path-pending")
    expect(_style_value(title, "backdrop-filter-realized")).to_equal("blur(4px) saturate(170%)")
    expect(_style_value(title, "wm-material-surface-alpha-milli")).to_equal("878")
reset_wm_chrome_theme()
```

</details>

#### keeps AUTO and generic GPU WM targets on explicit solid material fallback

- keeps AUTO and generic GPU WM targets on explicit solid material fallback
   - Expected: body.color equals `opaque_fallback`
   - Expected: _style_value(body, "background-color") equals `opaque_fallback.to_string()`
   - Expected: _style_value(body, "backdrop-filter-capability") equals `unavailable`
   - Expected: _style_value(body, "backdrop-filter-requested-target") equals `solid-material`
   - Expected: _style_value(body, "backdrop-filter-fallback") equals `solid-material`
   - Expected: _style_value(body, "backdrop-filter-fallback-reason") equals `cpu-raster-backdrop-sampling-unavailable`
   - Expected: _style_value(body, "backdrop-filter-realized") equals ``
   - Expected: _style_value(body, "background-image") equals `none`
   - Expected: _style_value(body, "background-image-fallback") equals `solid-material`
   - Expected: title.color equals `0xFF000000u32 | (snapshot.material.active_title_fill_rgba & 0x00FFFFFFu32)`
   - Expected: _style_value(title, "wm-material-surface-alpha-milli") equals `1000`
   - Expected: _style_value(title, "backdrop-filter-capability") equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps AUTO and generic GPU WM targets on explicit solid material fallback")
val snapshot = _translucent_fallback_snapshot()
val opaque_fallback = 0xFF1F1F21u32
apply_theme_render_snapshot_to_wm_chrome(snapshot)
val auto_composition = shared_wm_scene_draw_ir_composition(_scene(), _taskbar(), DRAW_IR_BACKEND_AUTO, 1000, "09:41", 2)
val gpu_composition = shared_wm_scene_draw_ir_composition(_scene(), _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)

for composition in [auto_composition, gpu_composition]:
    val body = composition.batches[3].commands[0]
    val title = composition.batches[3].commands[1]
    expect(body.color).to_equal(opaque_fallback)
    expect(_style_value(body, "background-color")).to_equal(opaque_fallback.to_string())
    expect(_style_value(body, "backdrop-filter-capability")).to_equal("unavailable")
    expect(_style_value(body, "backdrop-filter-requested-target")).to_equal("solid-material")
    expect(_style_value(body, "backdrop-filter-fallback")).to_equal("solid-material")
    expect(_style_value(body, "backdrop-filter-fallback-reason")).to_equal("cpu-raster-backdrop-sampling-unavailable")
    expect(_style_value(body, "backdrop-filter-realized")).to_equal("")
    expect(_style_value(body, "background-image")).to_equal("none")
    expect(_style_value(body, "background-image-fallback")).to_equal("solid-material")
    expect(title.color).to_equal(0xFF000000u32 | (snapshot.material.active_title_fill_rgba & 0x00FFFFFFu32))
    expect(_style_value(title, "wm-material-surface-alpha-milli")).to_equal("1000")
    expect(_style_value(title, "backdrop-filter-capability")).to_equal("unavailable")
reset_wm_chrome_theme()
```

</details>

#### classifies concrete Metal as GPU while preserving Vulkan CPU planner semantics

- classifies concrete Metal as GPU while preserving Vulkan CPU planner semantics
   - Expected: metal_plan.selected_backend equals `DRAW_IR_BACKEND_GPU`
   - Expected: metal_unavailable.selected_backend equals `DRAW_IR_BACKEND_CPU`
   - Expected: vulkan_plan.selected_backend equals `DRAW_IR_BACKEND_CPU`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("classifies concrete Metal as GPU while preserving Vulkan CPU planner semantics")
val metal = shared_wm_scene_draw_ir_composition(_scene(), _taskbar(), "metal", 1000, "09:41", 2)
val vulkan = shared_wm_scene_draw_ir_composition(_scene(), _taskbar(), "vulkan", 1000, "09:41", 2)
val metal_plan = simple_2d_draw_ir_adv_composition_plan(metal, true)
val metal_unavailable = simple_2d_draw_ir_adv_composition_plan(metal, false)
val vulkan_plan = simple_2d_draw_ir_adv_composition_plan(vulkan, true)

expect(metal_plan.selected_backend).to_equal(DRAW_IR_BACKEND_GPU)
expect(metal_plan.fallback_required).to_be(false)
expect(metal_unavailable.selected_backend).to_equal(DRAW_IR_BACKEND_CPU)
expect(metal_unavailable.fallback_required).to_be(true)
expect(vulkan_plan.selected_backend).to_equal(DRAW_IR_BACKEND_CPU)
expect(vulkan_plan.fallback_required).to_be(false)
```

</details>

#### keeps active and inactive ordered mixed shadows in canonical DrawIR CSS

- keeps active and inactive ordered mixed shadows in canonical DrawIR CSS
   - Expected: _style_value(active_body, "box-shadow-raw") equals `1px 2px 3px 4px 1074864691, inset -5px 6px 7px 8px 2157554363`
   - Expected: _style_value(active_body, "box-shadow") equals `1px 2px 1074864691`
   - Expected: _style_value(active_body, "box-shadow-layer-count") equals `2`
   - Expected: _style_value(inactive_body, "box-shadow-raw") equals `inset 9px -10px 11px 12px 541349222, 13px 14px 15px 16px 813140121`
   - Expected: _style_value(inactive_body, "box-shadow") equals `13px 14px 813140121`
   - Expected: _style_value(inactive_body, "box-shadow-layer-count") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps active and inactive ordered mixed shadows in canonical DrawIR CSS")
val snapshot = _mixed_shadow_snapshot()
apply_theme_render_snapshot_to_wm_chrome(snapshot)
val composition = shared_wm_scene_draw_ir_composition(_scene(), _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)
val inactive_body = composition.batches[2].commands[0]
val active_body = composition.batches[3].commands[0]

expect(_style_value(active_body, "box-shadow-raw")).to_equal("1px 2px 3px 4px 1074864691, inset -5px 6px 7px 8px 2157554363")
expect(_style_value(active_body, "box-shadow")).to_equal("1px 2px 1074864691")
expect(_style_value(active_body, "box-shadow-layer-count")).to_equal("2")
expect(_style_value(inactive_body, "box-shadow-raw")).to_equal("inset 9px -10px 11px 12px 541349222, 13px 14px 15px 16px 813140121")
expect(_style_value(inactive_body, "box-shadow")).to_equal("13px 14px 813140121")
expect(_style_value(inactive_body, "box-shadow-layer-count")).to_equal("2")
reset_wm_chrome_theme()
```

</details>

#### lets Simple 2D plan a GPU-targeted WM composition with CPU fallback

- lets Simple 2D plan a GPU-targeted WM composition with CPU fallback
   - Expected: plan.composition_id equals `wm-composite`
   - Expected: plan.backend_target equals `DRAW_IR_BACKEND_GPU`
   - Expected: plan.selected_backend equals `cpu`
   - Expected: plan.batch_count equals `5`
   - Expected: plan.command_count equals `34`
   - Expected: plan.fallback_required is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lets Simple 2D plan a GPU-targeted WM composition with CPU fallback")
val composition = shared_wm_scene_draw_ir_composition(_scene(), _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)
val plan = simple_2d_draw_ir_adv_composition_plan(composition, false)

expect(plan.composition_id).to_equal("wm-composite")
expect(plan.backend_target).to_equal(DRAW_IR_BACKEND_GPU)
expect(plan.selected_backend).to_equal("cpu")
expect(plan.batch_count).to_equal(5)
expect(plan.command_count).to_equal(34)
expect(plan.fallback_required).to_equal(true)
```

</details>

#### changes composition scene key after drag and rejects stale event translation cache

- changes composition scene key after drag and rejects stale event translation cache
   - Expected: first.translation.scene_key equals `shared_wm_scene_layout_key(scene)`
   - Expected: moved_composition.scene_key equals `shared_wm_scene_layout_key(moved)`
   - Expected: moved_composition.batches[2].source.style_revision equals `original_composition.batches[2].source.style_revision`
   - Expected: stale_checked.translation.cache_hit is false
   - Expected: stale_checked.translation.stale_cache_rejected is true
   - Expected: stale_checked.translation.backend_target equals `DRAW_IR_BACKEND_GPU`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("changes composition scene key after drag and rejects stale event translation cache")
val scene = _scene()
val first = shared_wm_translate_pointer_event(scene, _taskbar(), 90, 125, "left", "down", 1000, "09:41", 2, DRAW_IR_BACKEND_GPU)
val moved = shared_wm_drag_window(scene, "surf2", 100, 0)
val original_composition = shared_wm_scene_draw_ir_composition(scene, _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)
val moved_composition = shared_wm_scene_draw_ir_composition(moved, _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)
val stale_checked = shared_wm_translate_pointer_event_cached(moved, _taskbar(), 90, 125, "left", "down", 1000, "09:41", 2, DRAW_IR_BACKEND_GPU, first.cache)

expect(first.translation.scene_key).to_equal(shared_wm_scene_layout_key(scene))
expect(moved_composition.scene_key).to_equal(shared_wm_scene_layout_key(moved))
expect(moved_composition.batches[2].source.style_revision).to_equal(original_composition.batches[2].source.style_revision)
expect(original_composition.batches[3].source.style_revision).to_contain("xy=80,120")
expect(moved_composition.batches[3].source.style_revision).to_contain("xy=180,120")
expect(stale_checked.translation.cache_hit).to_equal(false)
expect(stale_checked.translation.stale_cache_rejected).to_equal(true)
expect(stale_checked.translation.backend_target).to_equal(DRAW_IR_BACKEND_GPU)
```

</details>

#### maps translated WM events to draw processing batch context

- maps translated WM events to draw processing batch context
   - Expected: context.resolved is true
   - Expected: context.stale_scene_rejected is false
   - Expected: context.batch_id equals `window-win2`
   - Expected: context.surface_id equals `surf2`
   - Expected: context.component_id equals `win2`
   - Expected: context.component_kind equals `window`
   - Expected: context.batch_local_x equals `10`
   - Expected: context.batch_local_y equals `5`
   - Expected: context.backend_target equals `DRAW_IR_BACKEND_GPU`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps translated WM events to draw processing batch context")
val scene = _scene()
val composition = shared_wm_scene_draw_ir_composition(scene, _taskbar(), DRAW_IR_BACKEND_GPU, 1000, "09:41", 2)
val translation = shared_wm_translate_pointer_event(scene, _taskbar(), 90, 125, "left", "down", 1000, "09:41", 2, DRAW_IR_BACKEND_GPU).translation
val context = draw_ir_event_target_context(
    composition,
    translation.scene_key,
    translation.input_key,
    translation.action,
    translation.target_id,
    translation.component_kind,
    translation.local_x,
    translation.local_y,
    translation.backend_target
)

expect(context.resolved).to_equal(true)
expect(context.stale_scene_rejected).to_equal(false)
expect(context.batch_id).to_equal("window-win2")
expect(context.surface_id).to_equal("surf2")
expect(context.component_id).to_equal("win2")
expect(context.component_kind).to_equal("window")
expect(context.batch_local_x).to_equal(10)
expect(context.batch_local_y).to_equal(5)
expect(context.backend_target).to_equal(DRAW_IR_BACKEND_GPU)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering window scene Draw IR projection.
- window scene Draw IR projection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9aa6abbffe408473cc35d7300c789c8dd70ddeedf261c04913ebc1d919957b93`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9aa6abbffe408473cc35d7300c789c8dd70ddeedf261c04913ebc1d919957b93`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9aa6abbffe408473cc35d7300c789c8dd70ddeedf261c04913ebc1d919957b93`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **70/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/window_scene_draw_ir_spec.md (current)
findings: 8 blockers: 2
  narrative=100 structure=100 oracle=20
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=70; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/ui/window_scene_draw_ir_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/window_scene_draw_ir_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 21 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl:146:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains readable bitmap text when selected metrics are unavailable' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl:164:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'projects the window manager chrome and windows into composed Draw IR batches' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/window_scene_draw_ir_spec.spl:208:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps Draw IR source revisions stable for unchanged scenes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
