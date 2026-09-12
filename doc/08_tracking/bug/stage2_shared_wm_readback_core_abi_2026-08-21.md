# Stage 2 shared-WM readback is outside the core bootstrap ABI

**Status:** OPEN (unverified 2026-09-12)

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

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule D: filed after 2026-07-29, no runnable repro in the record); left open with a status line added since none existed. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification.
