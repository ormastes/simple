# SimpleOS Host GPU Image and Text Execution Contract Specification

| Tests | Active | Skipped | Pending |
|-------|--------|---------|---------|
| 3 | 3 | 0 | 0 |

## Scenarios

### admits resources only through the fresh-device Draw IR path with strict provenance

- Decode resources through the canonical host GPU wire.
- Require a full-target opaque RECT or IMAGE to initialize fresh device memory.
- Admit bounded smaller surfaces only with a real embedding ID. A Vulkan
  parent retains its session into a transparent per-surface framebuffer.
- Admit exact IMAGE commands plus bounded nearest-neighbor COPY and transparent
  src-over after opaque initialization, including opaque images clipped by a bounded named child surface, resolved
  TEXT, metadata-only WM RECT styles, and
  one nonzero-alpha first RECT that initializes a fresh transparent child after
  target/clip, font identity, glyph material, and framebuffer-area work
  preflight. Later translucent RECTs remain rejected.
- Route transient glyph quads through the same checked Vulkan image blend; font
  bytes and atlas/cache state remain owned by the canonical font renderer.
- Route an admitted nonzero-alpha RECT initializer through the same checked
  Vulkan src-over path; opaque RECTs retain the direct rect kernel.
- Read each Vulkan child before present, require device provenance, then apply
  embedding opacity through the checked parent Vulkan blend and release it.
- Reject unresolved, malformed, effect-styled, unsupported, unbounded scaled
  work, source/index arithmetic beyond the checked Vulkan
  shader limits, or target-disjoint work before promotion. Clipping never
  admits an empty intersection or an unnamed child.
- Require device readback, a positive backend handle, and zero skipped commands
  before reporting PASS.

<details>
<summary>Executable SSpec</summary>

Runnable source: 109 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source,
including the cached-opacity construction and hot-path scan contract.

```simple
val daemon = file_read("src/app/simpleos_gpu_host/daemon_runner.spl")
val draw_ir = file_read("src/lib/gc_async_mut/gpu/engine2d/draw_ir_adv.spl")
val target = file_read("src/lib/gc_async_mut/gpu/engine2d/draw_ir_target.spl")
val metal_target = file_read("src/lib/gc_async_mut/gpu/engine2d/draw_ir_target_metal.spl")
val font_renderer = file_read("src/lib/nogc_sync_mut/text_layout/font_renderer.spl")
val font_owner = file_read("src/lib/nogc_sync_mut/sffi/spl_fonts.spl")
expect(daemon).to_contain("engine2d_draw_ir_adv_fresh_device_composition_with_images")
expect(daemon).to_contain("result.readback_source == \"device_readback\"")
expect(daemon).to_contain("result.backend_handle > 0")
expect(daemon.contains("if decoded_resources.resources.len() > 0")).to_equal(false)
val fresh_start = draw_ir.index_of("fn engine2d_draw_ir_adv_fresh_device_composition_with_images")
expect(fresh_start).to_be_greater_than(-1)
val shared_start = _section_end(draw_ir, "fn _engine2d_draw_ir_adv_composition_with_images")
val fresh_body = draw_ir.slice(fresh_start, shared_start)
expect(fresh_body).to_contain("_engine2d_draw_ir_fresh_device_reason")
expect(fresh_body).to_contain("_engine2d_draw_ir_prepare_fresh_device_text")
expect(fresh_body).to_contain("preflight_rejected")
expect(fresh_body).to_contain("plan, 0, 1")
val exact_start = draw_ir.index_of("fn _engine2d_draw_ir_fresh_device_command_supported")
expect(exact_start).to_be_greater_than(-1)
val initializer_start = _section_end(draw_ir, "fn _engine2d_draw_ir_fresh_device_initializes_target")
val exact_body = draw_ir.slice(exact_start, initializer_start)
expect(exact_body).to_contain("command.kind == \"rect\"")
expect(exact_body).to_contain("command.kind == \"text\"")
val prepare_start = draw_ir.index_of("fn _engine2d_draw_ir_prepare_fresh_device_text")
expect(prepare_start).to_be_greater_than(-1)
val prepare_end = _section_end(draw_ir, "fn _engine2d_draw_ir_render_rect")
val prepare_body = draw_ir.slice(prepare_start, prepare_end)
expect(prepare_body).to_contain("eng.select_font_identity(identity)")
expect(prepare_body).to_contain("fonts.prepare_text")
expect(prepare_body).to_contain("font_atlas_subrect_pixels")
expect(prepare_body).to_contain("val max_pixel_work = width.to_i64() * height.to_i64()")
expect(prepare_body).to_contain("fresh-device-font-work-limit-exceeded")
expect(exact_body).to_contain("_engine2d_draw_ir_fresh_device_rect_style_supported")
expect(exact_body).to_contain("allow_clipped")
expect(exact_body).to_contain("allow_translucent_initializer")
expect(exact_body).to_contain("command.kind != \"image\"")
expect(exact_body).to_contain("val exact_size = command.width == image.width")
expect(exact_body).to_contain("val native_index_bounded")
expect(exact_body).to_contain("source_work <= 4294967295")
expect(exact_body).to_contain("(command.width.to_i64() - 1) * image.width.to_i64() <= 2147483647")
expect(exact_body).to_contain("(command.height.to_i64() - 1) * image.height.to_i64() <= 2147483647")
expect(exact_body).to_contain("native_index_bounded and")
expect(exact_body).to_contain("(exact_size or scaled_work_bounded)")
expect(exact_body).to_contain("scaled_work <= 2147483647")
expect(exact_body.contains("if not wholly_bounded:\n        return false")).to_equal(false)
expect(draw_ir).to_contain("_engine2d_draw_ir_image_is_opaque")
val image_struct_start = draw_ir.index_of(
    "struct Engine2dResolvedDrawIrImage:")
expect(image_struct_start).to_be_greater_than(-1)
val image_struct_end = _section_end(
    draw_ir, "struct Engine2dCssBackgroundPixels:")
val image_struct_body = draw_ir.slice(
    image_struct_start, image_struct_end)
expect(image_struct_body).to_contain("opaque: bool")
val image_constructor_start = draw_ir.index_of(
    "fn engine2d_resolved_draw_ir_image(")
expect(image_constructor_start).to_be_greater_than(-1)
val image_lookup_start = _section_end(
    draw_ir, "fn _engine2d_draw_ir_resolved_image_index(")
val image_constructor_body = draw_ir.slice(
    image_constructor_start, image_lookup_start)
expect(image_constructor_body).to_contain("for pixel in pixels:")
expect(image_constructor_body).to_contain("opaque: opaque")
val image_validation = image_constructor_body.index_of(
    "width > 0 and height > 0")
val image_alpha_scan = image_constructor_body.index_of(
    "for pixel in pixels:")
expect(image_validation).to_be_greater_than(-1)
expect(image_alpha_scan).to_be_greater_than(image_validation)
expect(image_constructor_body).to_contain(
    "pixels.len() == width.to_i64() * height.to_i64()")
expect(image_constructor_body).to_contain("if opaque:")
expect(draw_ir.split("for pixel in pixels:").len()).to_equal(2)
val opacity_start = draw_ir.index_of(
    "fn _engine2d_draw_ir_image_is_opaque(")
expect(opacity_start).to_be_greater_than(-1)
val opacity_end = _section_end(
    draw_ir, "fn _engine2d_draw_ir_unique_style_value(")
val opacity_body = draw_ir.slice(opacity_start, opacity_end)
expect(opacity_body).to_contain("image.opaque")
expect(opacity_body.contains("for pixel in image.pixels:")).to_equal(
    false)
val reason_start = draw_ir.index_of("fn _engine2d_draw_ir_fresh_device_reason")
expect(reason_start).to_be_greater_than(-1)
val reason_end = _section_end(draw_ir, "fn _engine2d_draw_ir_prepare_fresh_device_text")
val reason_body = draw_ir.slice(reason_start, reason_end)
expect(reason_body).to_contain("fresh-device-bounded-embedding-required")
expect(reason_body).to_contain("fresh-device-embedded-surface-required")
expect(reason_body).to_contain("fresh-device-opaque-full-target-first-command-required")
expect(target).to_contain("trait DrawIrRenderTarget:")
expect(target).to_contain("me draw_ir_create_offscreen")
expect(target).to_contain("me draw_ir_composite_readback")
expect(draw_ir).to_contain("eng.draw_ir_create_offscreen(")
expect(draw_ir).to_contain("eng.draw_ir_composite_readback(")
expect(draw_ir).to_contain("offscreen.shutdown()")
expect(draw_ir).to_contain("eng.draw_image_blend(x, y, image.width, image.height, image.pixels)")
expect(draw_ir).to_contain("if blend_images and not _engine2d_draw_ir_image_is_opaque(image)")
expect(draw_ir).to_contain("eng.draw_image_scaled_blend")
expect(draw_ir).to_contain("_engine2d_draw_ir_render_commands(offscreen, batch.commands, 0, 0, images, true)")
expect(metal_target).to_contain("fn draw_ir_font_evidence() -> DrawIrTargetFontEvidence?:")
expect(metal_target).to_contain("readback.device_identity != self.device_identity")
expect(metal_target).to_contain("engine2d_readback_with_identity(")
expect(metal_target).to_contain("readback.source == \"device_readback\"")
expect(metal_target).to_contain("readback.backend_handle > 0")
expect(font_renderer).to_contain("renderer.try_load_runtime_ttf(font_path)")
expect(font_renderer).to_contain("FontRasterizer.load_selected(ttf_path)")
expect(font_owner).to_contain("load_selected_font_file(ttf_path)")

```

</details>

### uses fenced tri-state cleanup and quarantines completion-unknown dependencies

- Submit the blit through the fenced tri-state helper.
- Discard commands that fail during recording.
- Quarantine dependent resources when completion remains unknown.
- Reject later rendering and return empty completion-unknown readback.

### shares the validated blit shader across standalone and session backends

- Compile `spirv_blit()` in both Vulkan initialization paths.
- Keep the checked exact and nearest-neighbor scaled IMAGE COPY/src-over route common to both
  paths with source dimensions in the validated 15-word/60-byte field layout
  inside the existing 64-byte push payload.

Executable source: `test/03_system/os/simpleos_host_gpu_image_execution_contract_spec.spl`.
