# Drawing Stack Parity Matrix — Simple vs Chromium

**Updated:** 2026-04-15  
**Branch:** renderer-phase-5-6 (worktree)  
**Total tests passing:** 224 (Phases 1–6) + ~225 new `it` blocks across Waves 1–3 (W1: 63, W2: 54, W3: 48 + 11 self-goldens)

---

## 1. Summary

| Metric | Value |
|--------|-------|
| Phases complete | 1, 2, 4, 5, 6 |
| Phases in-flight | 3 (text shaper), 7 (content/gui), 8 (reftest) |
| Total passing tests (pre-Phase 8) | 224 |
| Phase 8 new `it` blocks | 13 |
| Backend status | Stub (no real raster); Phase 8 final wires CPU + Vulkan |

### Per-Phase Count Table

| Phase | Files | LOC (approx) | Tests | Status |
|-------|-------|--------------|-------|--------|
| Phase 1 (Skia API) | 29 | ~1 800 | 158 | ✅ API surface; backend stub |
| Phase 1 final (CPU + Vulkan backends, Waves 1–2) | 4 | ~1 520 | 31 | ✅ raster_prims, shaders, CpuBackend dispatch, Vulkan pipeline cache |
| Phase 2 (blends/filters) | 9 | ~700 | 29 | ✅ |
| Phase 3 (text shaper) | 9 | ~600 | 12 | ✅ landed (script_detect, feature_tags, font_fallback, identity shaper) |
| Phase 3 final (Waves 1–3: OT parser + real shaper + AA glyph + LCD subpixel + COLRv1) | 5 | ~1 870 | 41 | ✅ ot_parser, rasterize, subpixel, real shaper (GSUB/GPOS/Arabic/Indic), colrv1 stub |
| Phase 4 (PaintArtifact + PropertyTrees) | 3 | ~360 | 12 | ✅ |
| Phase 5 (cc LayerTreeHost) | 6 | ~350 | 17 | ✅ |
| Phase 6 (viz CompositorFrame) | 7 | ~300 | 25 | ✅ |
| Phase 6 final (Waves 1–3: aggregator walker + compose + damage) | 3 | ~555 | 30 | ✅ aggregator_walker, aggregator_compose, damage |
| Phase 7 (content + gui) | 10 | ~640 | 14 | ✅ landed |
| Phase 8 (reftest harness) | 15 | ~700 | 13 | ✅ |
| Phase 8 final (Waves 1, 3: pixel-diff core + real diff + 11 scenes + 11 goldens) | 26 | ~990 | 28 | ✅ pixel_diff_core, pixel_diff, scenes/, goldens/ |

---

## 2. Skia Surface Coverage

### SkCanvas Methods

| Method | Chromium name | Status | Impl file |
|--------|--------------|--------|-----------|
| `save` | `SkCanvas::save` | ✅ impl | `src/lib/skia/entity/canvas.spl` |
| `saveLayer` | `SkCanvas::saveLayer` | ✅ impl | `src/lib/skia/entity/canvas.spl` |
| `saveLayerAlpha` | `SkCanvas::saveLayerAlpha` | 🟢 partial | `src/lib/skia/entity/canvas.spl` |
| `restore` | `SkCanvas::restore` | ✅ impl | `src/lib/skia/entity/canvas.spl` |
| `translate` | `SkCanvas::translate` | ✅ impl | `src/lib/skia/entity/canvas.spl` |
| `scale` | `SkCanvas::scale` | ✅ impl | `src/lib/skia/entity/canvas.spl` |
| `rotate` | `SkCanvas::rotate` | ✅ impl | `src/lib/skia/entity/canvas.spl` |
| `concat` | `SkCanvas::concat` | 🟢 partial | `src/lib/skia/entity/canvas.spl` |
| `setMatrix` | `SkCanvas::setMatrix` | ✅ impl | `src/lib/skia/entity/canvas.spl` |
| `clipRect` | `SkCanvas::clipRect` | ✅ impl | `src/lib/skia/entity/canvas.spl` |
| `clipPath` | `SkCanvas::clipPath` | 🟢 partial | `src/lib/skia/entity/canvas.spl` |
| `clipRRect` | `SkCanvas::clipRRect` | 🚧 Phase 3 | — |
| `drawRect` | `SkCanvas::drawRect` | ✅ impl | `src/lib/skia/entity/canvas.spl` |
| `drawRRect` | `SkCanvas::drawRRect` | ✅ impl | `src/lib/skia/entity/canvas.spl` |
| `drawOval` | `SkCanvas::drawOval` | ✅ impl | `src/lib/skia/entity/canvas.spl` |
| `drawCircle` | `SkCanvas::drawCircle` | ✅ impl | `src/lib/skia/entity/canvas.spl` |
| `drawPath` | `SkCanvas::drawPath` | ✅ impl | `src/lib/skia/entity/canvas.spl` |
| `drawImage` | `SkCanvas::drawImage` | ✅ impl | `src/lib/skia/entity/canvas.spl` |
| `drawImageRect` | `SkCanvas::drawImageRect` | 🟢 partial | `src/lib/skia/entity/canvas.spl` |
| `drawText` | `SkCanvas::drawSimpleText` | ✅ impl | `src/lib/skia/entity/canvas.spl` |
| `drawTextBlob` | `SkCanvas::drawTextBlob` | 🟢 partial | `src/lib/skia/entity/canvas.spl` |
| `drawPaint` | `SkCanvas::drawPaint` | ✅ impl | `src/lib/skia/entity/canvas.spl` |
| `drawPoints` | `SkCanvas::drawPoints` | 🟢 partial | `src/lib/skia/entity/canvas.spl` |
| `drawLine` | `SkCanvas::drawLine` | ✅ impl | `src/lib/skia/entity/canvas.spl` |
| `drawPicture` | `SkCanvas::drawPicture` | 🚧 Phase 8 final | — |
| `flush` | `GrDirectContext::flushAndSubmit` | ❌ deferred (GPU) | — |

### SkPaint Fields

| Field | Chromium name | Status | Impl file |
|-------|--------------|--------|-----------|
| `color` | `SkPaint::setColor` | ✅ impl | `src/lib/skia/entity/paint.spl` |
| `alpha` | `SkPaint::setAlpha` | ✅ impl | `src/lib/skia/entity/paint.spl` |
| `style` | `SkPaint::setStyle` | ✅ impl | `src/lib/skia/entity/paint.spl` |
| `stroke_width` | `SkPaint::setStrokeWidth` | ✅ impl | `src/lib/skia/entity/paint.spl` |
| `stroke_cap` | `SkPaint::setStrokeCap` | ✅ impl | `src/lib/skia/entity/paint.spl` |
| `stroke_join` | `SkPaint::setStrokeJoin` | ✅ impl | `src/lib/skia/entity/paint.spl` |
| `blend_mode` | `SkPaint::setBlendMode` | ✅ impl | `src/lib/skia/entity/paint.spl` |
| `shader` | `SkPaint::setShader` | 🟢 partial | `src/lib/skia/entity/paint.spl` |
| `color_filter` | `SkPaint::setColorFilter` | 🟢 partial | `src/lib/skia/entity/paint.spl` |
| `image_filter` | `SkPaint::setImageFilter` | 🟢 partial | `src/lib/skia/entity/paint.spl` |
| `mask_filter` | `SkPaint::setMaskFilter` | 🚧 Phase 3 | — |
| `path_effect` | `SkPaint::setPathEffect` | 🟢 partial | `src/lib/skia/entity/paint.spl` |
| `anti_alias` | `SkPaint::setAntiAlias` | ✅ impl | `src/lib/skia/entity/paint.spl` |
| `dither` | `SkPaint::setDither` | ❌ deferred | — |

### SkPath Verbs

| Verb | Chromium name | Status | Impl file |
|------|--------------|--------|-----------|
| `moveTo` | `SkPath::moveTo` | ✅ impl | `src/lib/skia/entity/path.spl` |
| `lineTo` | `SkPath::lineTo` | ✅ impl | `src/lib/skia/entity/path.spl` |
| `cubicTo` | `SkPath::cubicTo` | ✅ impl | `src/lib/skia/entity/path.spl` |
| `quadTo` | `SkPath::quadTo` | ✅ impl | `src/lib/skia/entity/path.spl` |
| `conicTo` | `SkPath::conicTo` | 🟢 partial | `src/lib/skia/entity/path.spl` |
| `close` | `SkPath::close` | ✅ impl | `src/lib/skia/entity/path.spl` |
| `arcTo` | `SkPath::arcTo` | 🚧 Phase 3 | — |
| `addRect` | `SkPath::addRect` | ✅ impl | `src/lib/skia/entity/path.spl` |
| `addOval` | `SkPath::addOval` | ✅ impl | `src/lib/skia/entity/path.spl` |
| `addRRect` | `SkPath::addRRect` | 🟢 partial | `src/lib/skia/entity/path.spl` |
| `addPath` | `SkPath::addPath` | 🚧 Phase 3 | — |
| `setFillType(Winding)` | `SkPathFillType::kWinding` | ✅ impl | `src/lib/skia/entity/enums.spl` |
| `setFillType(EvenOdd)` | `SkPathFillType::kEvenOdd` | ✅ impl | `src/lib/skia/entity/enums.spl` |
| `setFillType(InverseWinding)` | `SkPathFillType::kInverseWinding` | ✅ impl | `src/lib/skia/entity/enums.spl` |

---

## 3. Blink Paint Coverage

| Component | Chromium name | Status | Impl file |
|-----------|--------------|--------|-----------|
| PaintArtifact | `cc::PaintArtifact` | ✅ impl | `src/lib/cc/entity/paint_artifact.spl` (verify) |
| PaintChunk | `cc::PaintChunk` | ✅ impl | `src/lib/cc/entity/paint_artifact.spl` (verify) |
| PaintController | `blink::PaintController` | 🟢 partial | `src/lib/cc/entity/paint_artifact.spl` (verify) |
| PaintLayer | `blink::PaintLayer` | 🟢 partial | `src/lib/cc/entity/layer.spl` (verify) |
| PropertyTrees (transform) | `cc::TransformTree` | ✅ impl | `src/lib/cc/entity/property_tree.spl` |
| PropertyTrees (effect) | `cc::EffectTree` | ✅ impl | `src/lib/cc/entity/property_tree.spl` |
| PropertyTrees (clip) | `cc::ClipTree` | ✅ impl | `src/lib/cc/entity/property_tree.spl` |
| PropertyTrees (scroll) | `cc::ScrollTree` | 🟢 partial | `src/lib/cc/entity/property_tree.spl` |
| DisplayItemList | `cc::DisplayItemList` | 🟢 partial (SkPicture.ops list) | `src/lib/skia/entity/picture.spl` |
| PaintRecord | `cc::PaintRecord` | ✅ impl (SkPictureOp + 5 helper ctors) | `src/lib/skia/entity/picture.spl` |

---

## 4. cc Compositor Coverage

| Component | Chromium name | Status | Impl file |
|-----------|--------------|--------|-----------|
| LayerTreeHost | `cc::LayerTreeHost` | ✅ impl | `src/lib/cc/entity/layer.spl` |
| Layer | `cc::Layer` | ✅ impl | `src/lib/cc/entity/layer.spl` |
| PictureLayerImpl | `cc::PictureLayerImpl` | 🟢 partial | `src/lib/cc/entity/layer.spl` (verify) |
| TileManager | `cc::TileManager` | ✅ impl | `src/lib/cc/feature/tile_manager.spl` |
| RasterBufferProvider | `cc::RasterBufferProvider` | ✅ impl | `src/lib/cc/feature/raster_buffer_provider.spl` |
| RasterSource | `cc::RasterSource` | ✅ impl | `src/lib/cc/feature/raster_source.spl` |
| DamageTracker | `cc::DamageTracker` | ✅ impl (W3-6c) | `src/lib/viz/feature/damage.spl` |
| AnimationHost | `cc::AnimationHost` | ❌ deferred | — |
| Scheduler | `cc::Scheduler` | ❌ deferred | — |
| BeginFrameSource | `viz::BeginFrameSource` | ❌ deferred | — |

---

## 5. viz Coverage

| Component | Chromium name | Status | Impl file |
|-----------|--------------|--------|-----------|
| CompositorFrame | `viz::CompositorFrame` | ✅ impl | `src/lib/viz/entity/compositor_frame.spl` (verify) |
| RenderPass | `viz::CompositorRenderPass` | ✅ impl | `src/lib/viz/entity/compositor_frame.spl` (verify) |
| DrawQuad (SolidColor) | `viz::SolidColorDrawQuad` | ✅ impl | `src/lib/viz/entity/compositor_frame.spl` (verify) |
| DrawQuad (TileDrawQuad) | `viz::TileDrawQuad` | 🟢 partial | `src/lib/viz/entity/compositor_frame.spl` (verify) |
| DrawQuad (TextureDrawQuad) | `viz::TextureDrawQuad` | 🟢 partial | `src/lib/viz/entity/compositor_frame.spl` (verify) |
| DrawQuad (RenderPassDrawQuad) | `viz::CompositorRenderPassDrawQuad` | ✅ impl (W1-6a inlining) | `src/lib/viz/feature/aggregator_walker.spl` |
| DrawQuad (VideoHoleDrawQuad) | `viz::VideoHoleDrawQuad` | ❌ out-of-scope | see `out_of_scope_register.md` |
| DrawQuad (YUVVideoDrawQuad) | `viz::YUVVideoDrawQuad` | ❌ out-of-scope | see `out_of_scope_register.md` |
| SurfaceAggregator | `viz::SurfaceAggregator` | ✅ impl (W1-6a walker + W2-6b compose) | `src/lib/viz/feature/aggregator_{walker,compose}.spl` |
| DisplayCompositor | `viz::Display` | 🟢 partial | `src/lib/viz/entity/compositor_frame.spl` (verify) |
| FrameSink | `viz::CompositorFrameSink` | ❌ deferred | — |

---

## 6. content/gui Coverage

| Component | Chromium name | Status | Impl file |
|-----------|--------------|--------|-----------|
| WebContents | `content::WebContents` | 🚧 Phase 7 | — |
| RenderFrameHost | `content::RenderFrameHost` | 🚧 Phase 7 | — |
| RenderWidgetHostView | `content::RenderWidgetHostView` | 🚧 Phase 7 | — |
| OffscreenCanvas | `blink::OffscreenCanvas` | 🚧 Phase 7 | — |
| BrowserWindow | `chrome::BrowserWindow` | 🚧 Phase 7 | — |
| Menu | `views::MenuItemView` | 🚧 Phase 7 | — |
| IME | `ui::InputMethod` | ❌ deferred | — |
| PrintJob | `printing::PrintJob` | ❌ deferred | — |
| Accessibility (AX) | `ui::AXTree` | ❌ deferred | — |
| DevTools Protocol | `content::DevToolsAgentHost` | ❌ deferred | — |

---

## 7. Reftest Inventory

Each entry: scene file, cull rect, what it validates against a Chromium reference rendering once Phase 8 final lands real pixel diff.

| # | Scene | Cull Rect | Chromium API Validated |
|---|-------|-----------|------------------------|
| 1 | `test/reftest/parity/scenes/path_winding.spl` | 200×200 | `SkPath::setFillType(kWinding)` + star polygon fill |
| 2 | `test/reftest/parity/scenes/path_evenodd.spl` | 201×200 | `SkPath::setFillType(kEvenOdd)` + concentric rings |
| 3 | `test/reftest/parity/scenes/dashed_strokes.spl` | 200×201 | `SkDashPathEffect::Make` + stroked path |
| 4 | `test/reftest/parity/scenes/gradient_linear.spl` | 202×200 | `SkShader::MakeLinearGradient` two-stop |
| 5 | `test/reftest/parity/scenes/text_arabic.spl` | 200×202 | HarfBuzz RTL shaping → `SkCanvas::drawTextBlob` |
| 6 | `test/reftest/parity/scenes/porter_duff.spl` | 300×300 | `SkBlendMode::kSrcOver` saveLayer composite |
| 7 | `test/reftest/parity/scenes/mix_blend_mode.spl` | 301×300 | `SkBlendMode::kMultiply` — CSS `mix-blend-mode` |
| 8 | `test/reftest/parity/scenes/backdrop_filter.spl` | 300×301 | `saveLayer` with backdrop `SkImageFilter` blur |
| 9 | `test/reftest/parity/scenes/scroll_damage.spl` | 400×400 | `cc::DamageTracker` invalidation after 50 px scroll |
| 10 | `test/reftest/parity/scenes/transform_tree.spl` | 401×400 | `cc::TransformNode` rotate(45°) applied to layer |
| 11 | `test/reftest/parity/scenes/opacity_layer.spl` | 400×401 | `cc::EffectNode{opacity:0.5}` → `saveLayerAlpha(128)` |

Reference PNG files (`chromium_ref_file`) are empty strings in Phase 8; Phase 8 final populates them from headless Chrome screenshot captures.

---

## 8. CPU vs Vulkan Parity

Both backends are stubs. Real pixel comparison is pending Phase 8 final, which wires:

- **CPU backend** (`src/lib/skia/backend/cpu/backend.spl`) — software raster via Skia CPU pipeline.
- **Vulkan backend** (`src/lib/skia/backend/vulkan/backend.spl`) — GPU raster via Skia Vulkan pipeline.

| Test | CPU raster | Vulkan raster | Max allowed delta |
|------|-----------|---------------|-------------------|
| path_winding | pending Phase 8 final | pending Phase 1 final | 1 channel |
| path_evenodd | pending Phase 8 final | pending Phase 1 final | 1 channel |
| dashed_strokes | pending Phase 8 final | pending Phase 1 final | 1 channel |
| gradient_linear | pending Phase 8 final | pending Phase 1 final | 2 channel |
| text_arabic | pending Phase 8 final | pending Phase 1 final | 2 channel |
| porter_duff | pending Phase 8 final | pending Phase 1 final | 1 channel |
| mix_blend_mode | pending Phase 8 final | pending Phase 1 final | 1 channel |
| backdrop_filter | pending Phase 8 final | pending Phase 1 final | 3 channel |
| scroll_damage | pending Phase 8 final | pending Phase 1 final | 0 channel |
| transform_tree | pending Phase 8 final | pending Phase 1 final | 1 channel |
| opacity_layer | pending Phase 8 final | pending Phase 1 final | 1 channel |

---

## 9. Outstanding Gaps

The following Chromium features have no coverage in any current or planned phase:

| Gap | Chromium area | Blocker |
|-----|---------------|---------|
| WebGL / WebGPU | `gpu::gles2`, `gpu::webgpu` | Out-of-scope (see register) — Vulkan landed without ANGLE-equivalent |
| HDR / Display-P3 colour space | `gfx::ColorSpace`, `SkColorSpace` | Out-of-scope (see register) |
| COLRv1 emoji (full paint-graph) | `SkFontMgr` + OpenType COLRv1 | 🟢 skeleton landed (W3-3f); paint-graph composition deferred |
| Variable fonts (OpenType fvar/gvar) | HarfBuzz variation | 🟢 fvar axes parsed (W1-3a); avar mapping is identity stub |
| Video decode (VAAPI/NVDEC) | `media::VideoDecoder` | Out-of-scope (see register) |
| Real threaded compositor | `cc::Scheduler` + impl-thread | Out-of-scope (see register) |
| Metal backend (macOS) | `GrMtlGpu` | Out-of-scope (see register) |
| Direct3D 12 backend (Windows) | `GrD3DGpu` | Out-of-scope (see register) |
| Ink Overflow / CSS Masking | `blink::MaskPainter` | Phase 7 |
| CSS Container Queries | `blink::ContainerQueryEvaluator` | Phase 7 |
| WebXR / Immersive AR | `device::mojom::XRDevice` | Deferred indefinitely |

---

## 10. Phase Finals — Status

| Phase final | Status (2026-04-15) | Implementation |
|-------------|---------------------|----------------|
| **Phase 1 final** | ✅ landed (Waves 1–2) | `raster_prims.spl` (analytic AA primitives), `shaders.spl` (gradient/image/blend eval), `backend.spl` (CpuBackend dispatch over SkPicture.ops), `vulkan/backend.spl` (PipelineKey cache, ear-clipping triangulation, CommandBufferRecord). Vulkan ioctl edge remains `pass_todo`. |
| **Phase 3 final** | ✅ landed (Waves 1–3) | `ot_parser.spl` (cmap/glyf/hmtx/CFF/GSUB-GPOS skeleton/GDEF/fvar), `rasterize.spl` (analytic-AA scanline), `subpixel.spl` (FreeType 5-tap LCD filter + gamma), `shaper.spl` (script segmentation + GSUB/GPOS + Arabic joining + Devanagari Indic classification). COLRv1 paint-graph deferred. |
| **Phase 6 final** | ✅ landed (Waves 1–3) | `aggregator_walker.spl` (BFS surface walk + inline_render_pass with sqs remap), `aggregator_compose.spl` (Matrix3x3 mul, clip intersect, effect composition), `damage.spl` (union/intersect/aggregate, propagate up via 4-corner AABB transform). |
| **Phase 8 final** | ✅ landed (Waves 1, 3) | `pixel_diff_core.spl` (per-channel delta + mismatch_ratio + bitmap_diff_rect), `pixel_diff.spl` (compare_pictures drives CpuBackend → BitmapRef → summarize), 11 real scenes with distinct PaintOp recordings, 11 self-goldens (each rasters its own minimal SkPicture once). Real Chromium reference PNGs deferred (no headless Chrome harness in Simple yet — out-of-scope register). |

## 11. Out-of-Scope Items

See `doc/08_tracking/out_of_scope_register.md` for items intentionally deferred from the drawing-stack parity work.
