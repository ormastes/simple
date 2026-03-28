# Simple-Native 2D Game Engine - Known Limitations

**Date:** 2026-03-24
**Related:** [Requirements](../../plan/requirements/engine_2d.md) | [Plan](../../plan/engine_2d.md) | [Design](../../design/engine_2d.md) | [Research](../../research/engine_2d.md)

---

## LIM-001: Software Renderer Only (No GPU Acceleration)

**Severity:** High
**Status:** RESOLVED — `rt_sdl2_present_rgba()` in the SDL2 C runtime provides the present path. The pixel buffer is now uploaded and displayed each frame via SDL2.
**Description:** The engine uses a CPU-based software renderer (`SoftwareRenderer`) that writes pixels to an in-memory buffer, but the new-engine runtime path still has no connected framebuffer upload/present API. `GameLoop` can rasterize and request redraw, but that does not yet display the buffer in a real window on the Rust-driver path.
**Workaround:** Keep game resolution at 800x600 or lower. Minimize overdraw by culling off-screen sprites. Reduce particle counts.
**Future:** A future GPU backend can still sit behind the same `RenderCommand` interface.

## LIM-002: No Image File Loading

**Severity:** High
**Status:** RESOLVED — stb_image C runtime provides `rt_image_*` functions. `Texture.from_file()` now decodes PNG/JPG/BMP via the stb_image integration.
**Description:** `Texture.from_file()` is not functional. There is no `image_ffi.spl` to decode PNG/JPG/BMP files into pixel data. Textures can only be created programmatically via `Texture.create(width, height, pixels)`.
**Workaround:** Generate textures in code (solid colors, procedural patterns) or hard-code pixel arrays for small sprites.
**Future:** None — resolved.

## LIM-003: No Font/Text Rendering

**Severity:** Medium
**Status:** RESOLVED — stb_truetype C runtime provides `rt_font_*` functions for TrueType font loading and glyph rasterization.
**Description:** There is no font loading or text rendering capability. No `font_ffi.spl` exists to rasterize TrueType/OpenType fonts into glyph textures.
**Workaround:** Use geometric shapes (rectangles, lines) for UI elements. Display text via terminal output alongside the game window.
**Future:** None — resolved.

## LIM-004: No Texture Sampling in DrawSprite

**Severity:** Medium
**Description:** The `DrawSprite` render command draws sprites as colored rectangles using the sprite's tint color. Actual texture pixel sampling (reading from the texture's pixel buffer and blitting to the frame buffer) is not implemented in the software renderer.
**Workaround:** Use distinct colors per sprite type. Visual debugging works with colored rectangles. Combine with `DrawRect` for block-style graphics.
**Future:** Implement texture sampling in `SoftwareRenderer.execute_draw_sprite()` with bilinear filtering.

## LIM-005: Physics Debug Draw is Approximate

**Severity:** Low
**Description:** `PhysicsDebugDraw` renders circles as 16-segment polygons. At large radii or high zoom, the polygon approximation becomes visually noticeable.
**Workaround:** Increase segment count in `debug_draw.spl` for more accurate circles. Use debug draw only during development.
**Future:** Use the renderer's native `DrawCircle` command once the software renderer supports anti-aliased circle drawing.

## LIM-006: New Engine Window Runtime Not Wired In Rust Driver

**Severity:** High
**Status:** RESOLVED — Windowing now uses SDL2 via the C runtime (`rt_sdl2_*` family). The winit dependency has been removed.
**Description:** The Rust driver currently does not expose the `rt_winit_*` extern family used by the new 2D engine window/input layer. The demo therefore fails during semantic/runtime binding before a window can open.
**Workaround:** None in the Rust driver today. The old self-hosted path still contains these symbols but currently crashes in generic `run` / `check`, so it is not a valid fallback.
**Future:** None — resolved via SDL2 C runtime.

## LIM-007: New Engine Physics Runtime Not Wired In Rust Driver

**Severity:** High
**Status:** RESOLVED — Physics has been rewritten in pure Simple (no rapier2d dependency). The `rt_rapier2d_*` extern family is no longer required.
**Description:** The Rust driver also lacks the `rt_rapier2d_*` extern family used by `PhysicsWorld2D`, so even after module loading succeeds the demo cannot execute the real physics stack there yet.
**Workaround:** None.
**Future:** None — resolved via pure Simple physics implementation.

## LIM-008: Chained Method Calls Avoided

**Severity:** Low
**Description:** Simple's runtime has a known limitation where chained method calls (`node.get_child(0).set_position(v)`) can fail. All engine code uses intermediate `var` bindings.
**Workaround:** Always assign method results to a `var` before calling the next method. This is already followed throughout the engine source.
**Future:** Tracked as a Simple runtime fix. No engine-side change needed once resolved.

## LIM-009: Signals Use Text-Serialized Data

**Severity:** Low
**Description:** Simple's nested closure capture cannot modify outer variables. The signal/event system passes data as text-serialized payloads (`text` type) rather than typed structs. Subscribers must parse the payload string.
**Workaround:** Use a consistent serialization format (e.g., `"key1:value1,key2:value2"`) and parse in subscriber callbacks. Keep payloads simple.
**Future:** Once Simple supports mutable closure capture or adds typed channels, signals can carry typed payloads directly.

## LIM-010: Self-Hosted Driver Run/Check/Test Still Segfault

**Severity:** High
**Description:** The self-hosted `bin/simple_native` / `bin/simple_stage4` path still segfaults in generic `run`, `check`, and `test`, including trivial programs. This blocks the only runtime path that already contains the new engine's window symbols.
**Workaround:** Use the Rust driver for non-engine programs and engine code audit, but not for end-to-end new-engine execution.
**Future:** Fix the crash in `CompilerDriver.load_sources_impl()` and related generic driver flow.

---

## Summary

| ID | Severity | Status | Summary |
|----|----------|--------|---------|
| LIM-001 | High | RESOLVED | Software renderer present path (SDL2 `rt_sdl2_present_rgba`) |
| LIM-002 | High | RESOLVED | Image file loading (stb_image `rt_image_*`) |
| LIM-003 | Medium | RESOLVED | Font/text rendering (stb_truetype `rt_font_*`) |
| LIM-004 | Medium | Open | Sprites render as colored rects |
| LIM-005 | Low | Open | Circle debug draw is approximate |
| LIM-006 | High | RESOLVED | Window runtime (SDL2 C runtime replaces winit) |
| LIM-007 | High | RESOLVED | Physics runtime (pure Simple replaces rapier2d) |
| LIM-008 | Low | Open | Chained methods avoided |
| LIM-009 | Low | Open | Signal payloads are text-only |
| LIM-010 | High | Open | Self-hosted driver still segfaults |

## Cross-References

- **Requirements:** `doc/plan/requirements/engine_2d.md`
- **Plan:** `doc/plan/engine_2d.md`
- **Design:** `doc/design/engine_2d.md`
- **Research:** `doc/research/engine_2d.md`
- **Self:** `doc/tracking/bug/engine_2d_limitations.md`
- **Source:** `src/lib/nogc_sync_mut/engine/`, `src/lib/common/engine/`
- **Unit Tests:** `test/unit/lib/engine/`
- **Demo:** `examples/engine_2d_demo/main.spl`
