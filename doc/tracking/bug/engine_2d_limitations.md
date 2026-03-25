# Simple-Native 2D Game Engine - Known Limitations

**Date:** 2026-03-24
**Related:** [Requirements](../../plan/requirement/engine_2d.md) | [Plan](../../plan/engine_2d.md) | [Design](../../design/engine_2d.md) | [Research](../../research/engine_2d.md)

---

## LIM-001: Software Renderer Only (No GPU Acceleration)

**Severity:** High
**Description:** The engine uses a CPU-based software renderer (`SoftwareRenderer`) that writes pixels to an in-memory buffer, but the new-engine runtime path still has no connected framebuffer upload/present API. `GameLoop` can rasterize and request redraw, but that does not yet display the buffer in a real window on the Rust-driver path.
**Workaround:** Keep game resolution at 800x600 or lower. Minimize overdraw by culling off-screen sprites. Reduce particle counts.
**Future:** Add an explicit host present/upload API for packed RGBA frame buffers, then call it after `render_frame()`. A future GPU backend can still sit behind the same `RenderCommand` interface.

## LIM-002: No Image File Loading

**Severity:** High
**Description:** `Texture.from_file()` is not functional. There is no `image_ffi.spl` to decode PNG/JPG/BMP files into pixel data. Textures can only be created programmatically via `Texture.create(width, height, pixels)`.
**Workaround:** Generate textures in code (solid colors, procedural patterns) or hard-code pixel arrays for small sprites.
**Future:** Implement `image_ffi.spl` wrapping the `image` Rust crate to support common image formats.

## LIM-003: No Font/Text Rendering

**Severity:** Medium
**Description:** There is no font loading or text rendering capability. No `font_ffi.spl` exists to rasterize TrueType/OpenType fonts into glyph textures.
**Workaround:** Use geometric shapes (rectangles, lines) for UI elements. Display text via terminal output alongside the game window.
**Future:** Implement `font_ffi.spl` wrapping `fontdue` or `ab_glyph` for CPU-based glyph rasterization.

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
**Description:** The Rust driver currently does not expose the `rt_winit_*` extern family used by the new 2D engine window/input layer. The demo therefore fails during semantic/runtime binding before a window can open.
**Workaround:** None in the Rust driver today. The old self-hosted path still contains these symbols but currently crashes in generic `run` / `check`, so it is not a valid fallback.
**Future:** Add `rt_winit_*` runtime symbol registration and implementations to the Rust driver/runtime.

## LIM-007: New Engine Physics Runtime Not Wired In Rust Driver

**Severity:** High
**Description:** The Rust driver also lacks the `rt_rapier2d_*` extern family used by `PhysicsWorld2D`, so even after module loading succeeds the demo cannot execute the real physics stack there yet.
**Workaround:** None.
**Future:** Add `rt_rapier2d_*` runtime symbol registration and implementations to the Rust driver/runtime.

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

| ID | Severity | Summary |
|----|----------|---------|
| LIM-001 | High | Software renderer has no connected present path |
| LIM-002 | High | No image file loading |
| LIM-003 | Medium | No font/text rendering |
| LIM-004 | Medium | Sprites render as colored rects |
| LIM-005 | Low | Circle debug draw is approximate |
| LIM-006 | High | Rust driver lacks new-engine window runtime |
| LIM-007 | High | Rust driver lacks new-engine physics runtime |
| LIM-008 | Low | Chained methods avoided |
| LIM-009 | Low | Signal payloads are text-only |
| LIM-010 | High | Self-hosted driver still segfaults |

## Cross-References

- **Requirements:** `doc/requirement/engine_2d.md`
- **Plan:** `doc/plan/engine_2d.md`
- **Design:** `doc/design/engine_2d.md`
- **Research:** `doc/research/engine_2d.md`
- **Source:** `src/lib/nogc_sync_mut/engine/`, `src/lib/common/engine/`
- **Unit Tests:** `test/unit/lib/engine/`
- **Demo:** `examples/engine_2d_demo/main.spl`
