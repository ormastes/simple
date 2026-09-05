# Legacy Web GUI and WM Shared Font Route

> Proves the canonical Web, GUI widget, and WM producers retain resolved font

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Legacy Web GUI and WM Shared Font Route

Proves the canonical Web, GUI widget, and WM producers retain resolved font

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/legacy_web_gui_wm_font_route_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

Proves the canonical Web, GUI widget, and WM producers retain resolved font
identity and advance metadata in DrawIrComposition, then submit those same
compositions through the shared Engine2D CPU Draw IR route while the
caller-owned Draw IR metadata remains unchanged.
It also prevents canonical selected-font owners from importing the legacy game
font atlas or its owning GPU pipeline.

## Scenarios

### legacy Web GUI and WM shared font route

#### should preserve resolved font metadata and geometry through canonical CPU execution

- Render legacy Web GUI and WM text through DrawIR
- Resolve one selected font for layout and DrawIR paint
- Render legacy and WebIR text with one face identity
   - Expected: gui_identity equals `web_identity`
   - Expected: wm_identity equals `web_identity`
- var ink engine = Engine2D create with backend
- ink engine clear
- ink engine shutdown
- var blank engine = Engine2D create with backend
- blank engine clear
- blank engine shutdown
   - Expected: ink_result.pixels.len() equals `32 * 24`
- Check the production Simple Browser uses the same DrawIR route
   - Expected: host_web_source does not contain `simple_web_engine2d_render_html_pixels(html, width, height, backend_name)`
   - Expected: gui_host_source does not contain `browser_backend_collect_widget_draw_ir_commands`
   - Expected: gui_host_source does not contain `browser_backend_dispatch_prepared_draw_ir`
   - Expected: gui_host_source does not contain `web_render_artifact_with_runtime_dispatch_payload`
   - Expected: browser_source does not contain `simple_web_layout_render_html_software_pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 79 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render legacy Web GUI and WM text through DrawIR")
step("Resolve one selected font for layout and DrawIR paint")
val web_backend = WebRenderBackend.create("pure_simple", 160, 80)
val web = web_backend.render_html_to_draw_ir(
    "<html><body style='font-family:Noto Sans Mono;font-size:12px'>Web route</body></html>"
)
val gui = widget_tree_to_draw_ir_cpu(column("route-root", [label("route-label", "GUI route")]), 160, 80)
val wm = _wm_composition()

step("Render legacy and WebIR text with one face identity")
val web_identity = expect_legacy_draw_ir_font_parity(web, "Web route", 160, 80)
val gui_identity = expect_legacy_draw_ir_font_parity(gui, "GUI route", 160, 80)
val wm_identity = expect_legacy_draw_ir_font_parity(wm, "WM route", 320, 160)
expect(gui_identity).to_equal(web_identity)
expect(wm_identity).to_equal(web_identity)

val ink = WebRenderBackend.create("pure_simple", 32, 24).render_html_to_draw_ir(
    "<html><body style='background:transparent;color:black;font-family:Noto Sans Mono;font-size:12px'>A</body></html>"
)
val blank = WebRenderBackend.create("pure_simple", 32, 24).render_html_to_draw_ir(
    "<html><body style='background:transparent;color:black;font-family:Noto Sans Mono;font-size:12px'></body></html>"
)
var ink_engine = Engine2D.create_with_backend(32, 24, "cpu")
ink_engine.clear(0xffffffffu32)
val ink_result = engine2d_draw_ir_adv_composition(ink_engine, ink, false)
ink_engine.shutdown()
var blank_engine = Engine2D.create_with_backend(32, 24, "cpu")
blank_engine.clear(0xffffffffu32)
val blank_result = engine2d_draw_ir_adv_composition(blank_engine, blank, false)
blank_engine.shutdown()
expect(ink_result.pixels.len()).to_equal(32 * 24)
expect(_count_not_color(ink_result.pixels, 0xffffffffu32)).to_be_greater_than(0)
expect(_count_pixel_differences(ink_result.pixels, blank_result.pixels)).to_be_greater_than(0)

step("Check the production Simple Browser uses the same DrawIR route")
val host_web_source = rt_file_read_text("src/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer.spl")
expect(host_web_source).to_contain("simple_web_layout_render_html_pixels_engine2d(html, width, height, backend_name)")
expect(host_web_source).to_contain("simple_web_layout_render_html_readback_engine2d(html, width, height, backend_name)")
expect(host_web_source.contains("simple_web_engine2d_render_html_pixels(html, width, height, backend_name)")).to_equal(false)
val host_draw_ir_source = rt_file_read_text("src/lib/gc_async_mut/gpu/browser_engine/simple_web_layout_engine2d_fast.spl")
expect(host_draw_ir_source).to_contain("if result.skipped_command_count != 0:")
val gui_host_source = rt_file_read_text("src/app/ui.browser/backend.spl")
expect(gui_host_source).to_contain("widget_tree_to_draw_ir(root_node, self.width, self.height, DRAW_IR_BACKEND_GPU)")
expect(gui_host_source).to_contain("web_render_draw_ir_request_to_pixel_artifact(req, composition, self.gpu_backend_name)")
expect(gui_host_source.contains("browser_backend_collect_widget_draw_ir_commands")).to_equal(false)
expect(gui_host_source.contains("browser_backend_dispatch_prepared_draw_ir")).to_equal(false)
expect(gui_host_source.contains("web_render_artifact_with_runtime_dispatch_payload")).to_equal(false)
val gui_draw_ir_backend_source = rt_file_read_text("src/lib/gc_async_mut/ui/web_render_pixel_backend.spl")
expect(gui_draw_ir_backend_source).to_contain("engine2d_draw_ir_adv_composition(engine, composition, true)")
expect(gui_draw_ir_backend_source).to_contain("if result.skipped_command_count != 0")
expect(gui_draw_ir_backend_source).to_contain("if source == \"\": \"engine2d_pixel_readback\" else: source")
val browser_source = rt_file_read_text("src/os/apps/simple_browser/main.spl")
expect(browser_source).to_contain("simple_web_layout_render_html_engine2d_result")
expect(browser_source).to_contain("font_renderer_register_selected_bytes")
expect(browser_source).to_contain("selected_font_asset_candidates()")
expect(browser_source).to_contain("simpleos_font_asset_short_guest_path(candidate)")
expect(browser_source).to_contain("if registered_fonts != required_fonts")
expect(browser_source).to_contain("if result.skipped_command_count != 0")
expect(browser_source).to_contain("if non_bg <= 0 or not captured")
expect(browser_source.contains("simple_web_layout_render_html_software_pixels")).to_equal(false)
val mode_pos = browser_source.index_of("    font_renderer_use_registered_selected_bytes_only()") ?? -1
val register_pos = browser_source.index_of("font_renderer_register_selected_bytes(candidate.local_path, blob)") ?? -1
val catalog_pos = browser_source.index_of("if registered_fonts != required_fonts") ?? -1
val render_pos = browser_source.index_of("    val result = simple_web_layout_render_html_engine2d_result(") ?? -1
val capture_gate_pos = browser_source.index_of("    if non_bg <= 0 or not captured:") ?? -1
val marker_pos = browser_source.index_of("    serial_println(simple_browser_render_marker(") ?? -1
expect(mode_pos).to_be_greater_than(-1)
expect(register_pos).to_be_greater_than(mode_pos)
expect(catalog_pos).to_be_greater_than(register_pos)
expect(render_pos).to_be_greater_than(catalog_pos)
expect(capture_gate_pos).to_be_greater_than(render_pos)
expect(marker_pos).to_be_greater_than(capture_gate_pos)

val vfs_source = rt_file_read_text("src/os/services/vfs/vfs_init.spl")
val adapter_source = rt_file_read_text("src/os/services/vfs/c_nvme_block_adapter.spl")
val boot_vfs_source = rt_file_read_text("src/os/services/vfs/vfs_boot_init.spl")
expect(vfs_source).to_contain("FAT32_PATH_READ_BUFFER_MAX: u64 = 33554432")
expect(adapter_source).to_contain("FAT32_PATH_READ_BUFFER_MAX: u64 = 33554432")
expect(boot_vfs_source).to_contain("PURE_FAT32_FILE_READ_MAX: u64 = 33554432")
```

</details>

#### should keep canonical selected-font owners independent from the legacy game atlas

- Verify canonical selected-font owners do not depend on the legacy game font atlas
   - Expected: source does not contain `use std.nogc_sync_mut.engine.render.font_atlas`
   - Expected: source does not contain `use std.nogc_async_mut.engine.render.font_atlas`
   - Expected: source does not contain `use std.nogc_sync_mut.engine.render.gpu_pipeline`
   - Expected: source does not contain `use std.gc_async_mut.engine.render.gpu_pipeline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify canonical selected-font owners do not depend on the legacy game font atlas")
val canonical_font_owners = [
    "src/lib/nogc_sync_mut/text_layout/font_renderer.spl",
    "src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl",
    "src/lib/common/ui/draw_ir.spl",
    "src/lib/common/ui/draw_ir_sdn.spl",
    "src/lib/common/ui/widget_draw_ir.spl",
    "src/lib/common/ui/window_scene.spl",
    "src/lib/common/ui/window_scene_draw_ir.spl",
    "src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl",
    "src/lib/gc_async_mut/gpu/engine2d/engine.spl",
    "src/lib/gc_async_mut/gpu/engine3d/engine.spl",
    "src/os/compositor/engine2d_wm_frame_executor.spl"
]
for path in canonical_font_owners:
    val source = rt_file_read_text(path)
    expect(source.len()).to_be_greater_than(0)
    expect(source.contains("use std.nogc_sync_mut.engine.render.font_atlas")).to_equal(false)
    expect(source.contains("use std.nogc_async_mut.engine.render.font_atlas")).to_equal(false)
    expect(source.contains("use std.nogc_sync_mut.engine.render.gpu_pipeline")).to_equal(false)
    expect(source.contains("use std.gc_async_mut.engine.render.gpu_pipeline")).to_equal(false)
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


</details>
