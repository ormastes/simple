# 2D Library Consolidation Report

Generated: 2026-03-25

## Canonical Types (Engine)

| Type | Path | Purpose |
|------|------|---------|
| `EngineColor` | `src/lib/common/engine/color.spl` | Normalized f64 RGBA color with lerp, blend, hex, presets |
| `Rect2` | `src/lib/common/engine/rect.spl` | Axis-aligned rect (f64 x/y/w/h) with contains, intersects, center |
| `Vec2` | `src/lib/common/engine/math2d.spl` | 2D vector (f64 x/y) with add, sub, scale, dot, length, normalize |
| `Transform2D` | `src/lib/common/engine/math2d.spl` | 3x2 affine matrix with translate, rotate, scale, multiply, inverse |
| `Angle` | `src/lib/common/engine/units.spl` | Strongly-typed angle (radians) with to_degrees |
| `ZIndex` | `src/lib/common/engine/units.spl` | Strongly-typed z-order value (i64) |
| `Seconds` | `src/lib/common/engine/units.spl` | Strongly-typed time duration (f64) |
| `Vertex2D` | `src/lib/nogc_sync_mut/engine/render/types.spl` | Per-vertex data: position, UV, color tint (f64) |
| `BlendMode` | `src/lib/nogc_sync_mut/engine/render/types.spl` | Pixel blending enum: Alpha, Additive, Multiply, Opaque |
| `RenderCommand` | `src/lib/nogc_sync_mut/engine/render/command.spl` | Draw command enum: Clear, DrawRect, DrawCircle, DrawLine, DrawSprite, DrawTriangles |
| `RenderCommandBuffer` | `src/lib/nogc_sync_mut/engine/render/command.spl` | Frame command accumulator |
| `SoftwareRenderer` | `src/lib/nogc_sync_mut/engine/render/pipeline.spl` | CPU rasterizer with pixel buffer, clear, render_frame |
| `Material2D` | `src/lib/nogc_sync_mut/engine/render/material.spl` | Surface appearance: solid, textured, tinted |

## Other 2D Code in Engine/Library (Non-Browser)

| Type | Path | Notes |
|------|------|-------|
| `Color` (i64) | `src/lib/common/color/types.spl` | Standalone i64 RGBA Color class with named constants, from_rgb, from_rgba |
| `Point2D` | `src/lib/nogc_sync_mut/io/graphics2d_ffi.spl:86` | FFI struct (f64 x/y) — wraps Lyon tessellation library |
| `Vector2D` | `src/lib/nogc_sync_mut/io/graphics2d_ffi.spl:90` | FFI struct (f64 x/y) — wraps Lyon |
| `Rect` | `src/lib/nogc_sync_mut/io/graphics2d_ffi.spl:94` | FFI struct (f64 x/y/w/h) — wraps Lyon |
| `Bounds` | `src/lib/nogc_sync_mut/io/graphics2d_ffi.spl:100` | FFI struct (min_x/min_y/max_x/max_y) with width/height/center |
| `Transform2D` (FFI) | `src/lib/nogc_sync_mut/io/graphics2d_ffi.spl:462` | FFI handle wrapper (i64 handle) — wraps Lyon transforms |
| `PathBuilder` | `src/lib/nogc_sync_mut/io/graphics2d_ffi.spl:121` | FFI path builder for tessellation |
| `Size` | `src/lib/nogc_sync_mut/io/window_ffi.spl:213` | Window size struct (i64 width/height) |
| `Position` | `src/lib/nogc_sync_mut/io/window_ffi.spl:217` | Window position struct (i64 x/y) |
| `Pointcut` | `src/lib/nogc_sync_mut/src/aop.spl:17` | AOP pointcut — not geometry, false positive |

## Duplications Found

### High-Confidence Duplications (Clear Engine Equivalent)

| Browser Type | File | Engine Equivalent | Similarity | Action |
|-------------|------|-------------------|------------|--------|
| `Color` (i64 r/g/b/a) | `entity/dom/paint_types.spl:4` | `std.common.color.types.Color` (i64 r/g/b/a) | **Exact duplicate** — same fields, same rgb/rgba/black/white constructors | Replace with `use std.common.color.types.Color`; add `transparent()` to stdlib Color if missing |
| `CSSValue.Color(r,g,b,a)` | `entity/dom/css_types.spl:8` | `std.common.color.types.Color` | **Partial overlap** — inlines r/g/b/a fields instead of wrapping Color | Refactor to `CSSValue.Color(color: Color)` |
| `DamageRect` (f64 x/y/w/h) | `feature/composite/damage_tracker.spl:11` | `std.common.engine.rect.Rect2` (f64 x/y/w/h) | **Near-duplicate** — same fields, same right()/bottom(); Rect2 has more (contains, intersects, center) | Replace with Rect2 |
| `DamageRect` (test copy) | `test/composite/damage_tracking_spec.spl:4` | `std.common.engine.rect.Rect2` | **Near-duplicate** — identical to damage_tracker.spl copy | Replace with Rect2 |
| `DisplayItem.z_index: i64` | `entity/dom/paint_types.spl:57` | `std.common.engine.units.ZIndex` | **Partial overlap** — bare i64 vs. strongly-typed wrapper | Wrap with ZIndex |
| `StackingContext.z_index: i64` | `test/paint/stacking_context_spec.spl:6` | `std.common.engine.units.ZIndex` | **Partial overlap** — bare i64 vs. strongly-typed wrapper | Wrap with ZIndex |

### Conceptual Overlaps (Shared Abstraction Opportunity)

| Browser Type | File | Engine Equivalent | Similarity | Action |
|-------------|------|-------------------|------------|--------|
| `PaintOp` enum | `entity/dom/paint_types.spl:39` | `RenderCommand` enum (`nogc_sync_mut/engine/render/command.spl`) | **Conceptual overlap** — both are display-list command enums; PaintOp has FillRect/DrawText/DrawBorder/DrawImage/PushClip/PushOpacity; RenderCommand has Clear/DrawRect/DrawCircle/DrawLine/DrawSprite/DrawTriangles | Evaluate shared 2D display-list base; PaintOp is CSS-specific, RenderCommand is game-specific — a common base could unify FillRect/DrawRect |
| `CanvasOp` enum | `entity/media/canvas_types.spl:8` | `RenderCommand` + `PathBuilder` (graphics2d_ffi) | **Conceptual overlap** — canvas ops (MoveTo, LineTo, ArcTo, Fill, Stroke) parallel PathBuilder API; DrawImage parallels RenderCommand.DrawSprite | Evaluate bridging CanvasOp to PathBuilder + RenderCommand pipeline |
| `LayoutBox` (x/y/w/h fields) | `entity/dom/box_types.spl:36` | `std.common.engine.rect.Rect2` | **Partial overlap** — LayoutBox embeds x/y/width/height inline; Rect2 could replace the geometry portion | Compose LayoutBox with Rect2 field for content rect |
| `CanvasOp` colors as text | `entity/media/canvas_types.spl:13-14` | `std.common.color.types.Color` or `EngineColor` | **Weak overlap** — colors are stored as text ("#000000") instead of typed Color | Use Color type instead of text for fill/stroke style |
| `ImageData.data: List<i64>` | `entity/media/image_types.spl:17` | `SoftwareRenderer` pixel buffer (`[i64]` packed RGBA) | **Format overlap** — both store pixels as i64 lists; engine uses `(r<<24)\|(g<<16)\|(b<<8)\|a` packing | Align pixel packing format; share pack/unpack utilities |

### Browser-Specific Types (No Engine Equivalent)

| Type | File | Notes |
|------|------|-------|
| `BoxKind` | `entity/dom/box_types.spl:4` | CSS-specific (Block/Inline/Flex/Grid/Table) — no engine equivalent |
| `BoxModel` | `entity/dom/box_types.spl:15` | CSS box model (margin/border/padding) — no engine equivalent |
| `GradientStop` | `entity/dom/paint_types.spl:25` | CSS gradient stop — no engine equivalent |
| `Gradient` | `entity/dom/paint_types.spl:32` | CSS gradient — no engine equivalent |
| `DisplayList` | `entity/dom/paint_types.spl:49` | CSS display list — engine uses RenderCommandBuffer (similar but game-specific) |
| `CSSValue` | `entity/dom/css_types.spl:4` | CSS value enum — domain-specific, no engine equivalent |
| `CSSDeclaration` | `entity/dom/css_types.spl:15` | CSS declaration — domain-specific |
| `CSSRule` | `entity/dom/css_types.spl:39` | CSS rule — domain-specific |
| `Selector`/`SelectorPart` | `entity/dom/css_types.spl:23,33` | CSS selectors — domain-specific |
| `Specificity` | `entity/dom/css_types.spl:46` | CSS specificity — domain-specific |
| `CanvasContext` | `entity/media/canvas_types.spl:24` | HTML Canvas API context — browser-specific |
| `Path2D` | `entity/media/canvas_types.spl:18` | Canvas path — browser could bridge to PathBuilder from graphics2d_ffi |
| `ImageFormat` | `entity/media/image_types.spl:4` | Web image format enum — browser-specific |
| `DecodedFrame` | `entity/media/image_types.spl:22` | Animated frame — browser-specific |
| `GpuSurface` | `feature/gpu/surface.spl:35` | GPU render target — browser-specific (could share with engine GPU backend) |
| `SurfaceFormat` | `feature/gpu/surface.spl:19` | Pixel format enum — browser-specific |
| `FontFace`/`GlyphMetrics`/`FontCollection` | `entity/media/font_types.spl` | Font types — browser-specific |
| `PaintToCompositeBridge` | `transform/paint_to_composite.spl:18` | Browser compositor bridge — browser-specific |
| `DamageTracker` | `feature/composite/damage_tracker.spl:33` | Damage region manager — browser-specific (but DamageRect inside it duplicates Rect2) |

## Library-Internal Duplications (Not Browser)

| Type | File | Canonical | Notes |
|------|------|-----------|-------|
| `Point2D` (FFI) | `graphics2d_ffi.spl:86` | `Vec2` (`engine/math2d.spl`) | Same f64 x/y fields; FFI needs raw struct so this is intentional for C interop |
| `Vector2D` (FFI) | `graphics2d_ffi.spl:90` | `Vec2` (`engine/math2d.spl`) | Same f64 x/y fields; intentional FFI duplicate |
| `Rect` (FFI) | `graphics2d_ffi.spl:94` | `Rect2` (`engine/rect.spl`) | Same f64 x/y/w/h fields; intentional FFI duplicate |
| `Transform2D` (FFI) | `graphics2d_ffi.spl:462` | `Transform2D` (`engine/math2d.spl`) | FFI version is handle-based (i64 handle); engine version is pure math (6 matrix fields) |
| `Color` (common/color) | `common/color/types.spl:17` | `EngineColor` (`engine/color.spl`) | Both RGBA; Color uses i64 (0-255), EngineColor uses f64 (0.0-1.0) — different precision tiers, both needed |
| `Size` (window_ffi) | `window_ffi.spl:213` | No exact equivalent | i64 width/height; Vec2 is f64 — intentional for window system interop |

## Recommendations

1. **Immediate wins (exact/near duplicates):**
   - Replace `browser Color` in `paint_types.spl` with `std.common.color.types.Color` — identical type
   - Replace `DamageRect` (2 locations) with `std.common.engine.rect.Rect2` — gains contains_point(), intersects(), center()
   - Add `transparent()` constructor to `std.common.color.types.Color` if not present (browser Color has it)

2. **Low-effort refactors:**
   - Wrap `CSSValue.Color(r,g,b,a)` to `CSSValue.Color(color: Color)` for type safety
   - Replace bare `z_index: i64` in `DisplayItem` and `StackingContext` with `ZIndex` wrapper
   - Compose `LayoutBox` with a `Rect2` field instead of inline x/y/width/height

3. **Medium-effort shared abstractions:**
   - Create a common 2D display-list base that both PaintOp and RenderCommand can extend
   - Bridge `CanvasOp` path commands through `PathBuilder` from graphics2d_ffi for GPU-backed canvas
   - Align `ImageData` pixel format with engine's packed RGBA convention

4. **Intentional duplicates (leave as-is):**
   - FFI structs in `graphics2d_ffi.spl` (`Point2D`, `Vector2D`, `Rect`, `Transform2D`) — need raw C-compatible layout
   - `Color` (i64) vs `EngineColor` (f64) — different precision tiers serve different subsystems
   - `Size`/`Position` in window_ffi — i64 window system interop types

5. **Consolidation order:** Color first (safest, most used), then DamageRect/Rect2, then z_index/ZIndex, then LayoutBox composition, then display-list unification last (highest risk).

## TODO Comments Added

| File | TODO Summary |
|------|-------------|
| `examples/browser/entity/dom/paint_types.spl` | Color -> std.common.color.types.Color; PaintOp -> Rect2 params + RenderCommand parallel; DisplayItem -> ZIndex |
| `examples/browser/entity/dom/box_types.spl` | LayoutBox -> compose with Rect2 |
| `examples/browser/entity/dom/css_types.spl` | CSSValue.Color -> wrap std.common.color.types.Color |
| `examples/browser/entity/media/canvas_types.spl` | CanvasOp colors text -> Color type; points -> Vec2; Path2D -> PathBuilder |
| `examples/browser/entity/media/image_types.spl` | ImageData pixel format -> align with engine packed RGBA |
| `examples/browser/feature/composite/damage_tracker.spl` | DamageRect -> Rect2 |
| `examples/browser/test/composite/damage_tracking_spec.spl` | DamageRect -> Rect2 |
| `examples/browser/test/paint/display_list_spec.spl` | PaintStyle colors -> follow Color migration |
| `examples/browser/test/paint/stacking_context_spec.spl` | StackingContext.z_index -> ZIndex |
