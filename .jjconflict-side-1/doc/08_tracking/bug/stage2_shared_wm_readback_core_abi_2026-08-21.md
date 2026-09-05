# Stage 2 shared-WM readback is outside the core bootstrap ABI

## Evidence

The Phase 2 compiler successfully compiled the production closure rooted at
`test/fixtures/native_arm64_render_phase2/main.spl`, then the native linker
failed on `_rt_u32s_from_raw`, referenced by
`shared_wm_pixel_buffer_pixels` in `common.ui.window_scene_draw_ir`.

The selected runtime lane was `core-c-bootstrap`; its diagnostic states that
the lane intentionally exposes only the Simple/C core ABI. This prevents a
Phase-2-only executable from proving production shared-WM framebuffer
readback, even though smaller framebuffer color and compositor-decoration
closures compile and execute successfully.

## Required resolution

Either admit and implement `rt_u32s_from_raw` in the Stage 2 core bootstrap
runtime, provide a bootstrap-safe readback implementation, or defer this exact
production closure to an attested Phase 3 compiler/runtime. After resolution,
build and execute the fixture, then use the attested ARM64 desktop artifact for
the QEMU screendump gate.
