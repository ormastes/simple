# Simple-Native 2D Game Engine - Known Limitations

**Date:** 2026-03-24
**Related:** [Requirements](../requirement/engine_2d.md) | [Plan](../plan/engine_2d.md) | [Design](../design/engine_2d.md) | [Research](../research/engine_2d.md)

---

## LIM-001: Software Renderer Only (No GPU Acceleration)

**Severity:** Medium
**Description:** The engine uses a CPU-based software renderer (`SoftwareRenderer`) that writes pixels to a buffer and presents via `graphics2d_ffi`. There is no GPU-accelerated rendering path. Performance degrades at high resolutions or with many draw calls.
**Workaround:** Keep game resolution at 800x600 or lower. Minimize overdraw by culling off-screen sprites. Reduce particle counts.
**Future:** Phase 8 adds a Vulkan render backend behind the same `RenderCommand` interface. GPU modules already exist in `src/lib/nogc_sync_mut/gpu/`.

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

## LIM-006: Chained Method Calls Avoided

**Severity:** Low
**Description:** Simple's runtime has a known limitation where chained method calls (`node.get_child(0).set_position(v)`) can fail. All engine code uses intermediate `var` bindings.
**Workaround:** Always assign method results to a `var` before calling the next method. This is already followed throughout the engine source.
**Future:** Tracked as a Simple runtime fix. No engine-side change needed once resolved.

## LIM-007: Signals Use Text-Serialized Data

**Severity:** Low
**Description:** Simple's nested closure capture cannot modify outer variables. The signal/event system passes data as text-serialized payloads (`text` type) rather than typed structs. Subscribers must parse the payload string.
**Workaround:** Use a consistent serialization format (e.g., `"key1:value1,key2:value2"`) and parse in subscriber callbacks. Keep payloads simple.
**Future:** Once Simple supports mutable closure capture or adds typed channels, signals can carry typed payloads directly.

## LIM-008: Bootstrap Binary Cannot Run Tests

**Severity:** Low
**Description:** The Rust bootstrap binary (`src/compiler_rust/target/bootstrap/simple`) does not support the `test` command. Unit tests require the full self-hosted `bin/release/simple` binary.
**Workaround:** Build the self-hosted binary first (`scripts/bootstrap/bootstrap-from-scratch.sh`), then run tests with `bin/simple test test/unit/lib/engine/`.
**Future:** Not applicable. This is a bootstrap limitation by design.

---

## Summary

| ID | Severity | Summary |
|----|----------|---------|
| LIM-001 | Medium | Software renderer only, no GPU |
| LIM-002 | High | No image file loading |
| LIM-003 | Medium | No font/text rendering |
| LIM-004 | Medium | Sprites render as colored rects |
| LIM-005 | Low | Circle debug draw is approximate |
| LIM-006 | Low | Chained methods avoided |
| LIM-007 | Low | Signal payloads are text-only |
| LIM-008 | Low | Bootstrap binary lacks test command |

## Cross-References

- **Requirements:** `doc/requirement/engine_2d.md`
- **Plan:** `doc/plan/engine_2d.md`
- **Design:** `doc/design/engine_2d.md`
- **Research:** `doc/research/engine_2d.md`
- **Source:** `src/lib/nogc_sync_mut/engine/`, `src/lib/common/engine/`
- **Unit Tests:** `test/unit/lib/engine/`
- **Demo:** `examples/engine_2d_demo/main.spl`
