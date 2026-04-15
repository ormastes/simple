# Drawing Stack Parity Matrix — Simple vs Chromium

**Updated:** 2026-04-14  
**Branch:** renderer-phase-5-6  
**Total tests passing:** 224 (Phases 1–6) + Phase 8 additions (≥13 new `it` blocks)

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
| Phase 2 (blends/filters) | 9 | ~700 | 29 | ✅ |
| Phase 4 (PaintArtifact + PropertyTrees) | 3 | ~360 | 12 | ✅ |
| Phase 5 (cc LayerTreeHost) | 6 | ~350 | 17 | ✅ |
| Phase 6 (viz CompositorFrame) | 7 | ~300 | 25 | ✅ |
| Phase 3 (text shaper) | 9 | TBD | TBD | landing in parallel |
| Phase 7 (content + gui) | 10 | TBD | TBD | landing in parallel |
| Phase 8 (reftest harness) | 15 | ~700 | 13+ | this task |

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
| DisplayItemList | `cc::DisplayItemList` | 🚧 Phase 7 | — |
| PaintRecord | `cc::PaintRecord` | 🚧 Phase 7 | — |

---

## 4. cc Compositor Coverage

| Component | Chromium name | Status | Impl file |
|-----------|--------------|--------|-----------|
| LayerTreeHost | `cc::LayerTreeHost` | ✅ impl | `src/lib/cc/entity/layer.spl` |
| Layer | `cc::Layer` | ✅ impl | `src/lib/cc/entity/layer.spl` |
| PictureLayerImpl | `cc::PictureLayerImpl` | 🟢 partial | `src/lib/cc/entity/layer.spl` (verify) |
| TileManager | `cc::TileManager` | 🚧 Phase 5 final | — |
| RasterBufferProvider | `cc::RasterBufferProvider` | 🚧 Phase 5 final | — |
| RasterSource | `cc::RasterSource` | 🚧 Phase 5 final | — |
| DamageTracker | `cc::DamageTracker` | 🚧 Phase 8 final | — |
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
| DrawQuad (RenderPassDrawQuad) | `viz::CompositorRenderPassDrawQuad` | 🚧 Phase 6 final | — |
| DrawQuad (VideoHoleDrawQuad) | `viz::VideoHoleDrawQuad` | ❌ deferred | — |
| DrawQuad (YUVVideoDrawQuad) | `viz::YUVVideoDrawQuad` | ❌ deferred | — |
| SurfaceAggregator | `viz::SurfaceAggregator` | 🚧 Phase 6 final | — |
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
| WebGL / WebGPU | `gpu::gles2`, `gpu::webgpu` | Needs real Vulkan backend (Phase 1 final) |
| HDR / Display-P3 colour space | `gfx::ColorSpace`, `SkColorSpace` | No colour-managed surface stub yet |
| COLRv1 emoji | `SkFontMgr` + OpenType COLRv1 | Needs Phase 3 text shaper final |
| Variable fonts (OpenType fvar/gvar) | HarfBuzz variation | Phase 3 final |
| Video decode (VAAPI/NVDEC) | `media::VideoDecoder` | Out of scope for drawing stack |
| Real threaded compositor | `cc::Scheduler` + impl-thread | Needs async runtime integration |
| Metal backend (macOS) | `GrMtlGpu` | Platform-specific; x86_64 QEMU target only |
| Direct3D 12 backend (Windows) | `GrD3DGpu` | Platform-specific |
| Ink Overflow / CSS Masking | `blink::MaskPainter` | Phase 7 |
| CSS Container Queries | `blink::ContainerQueryEvaluator` | Phase 7 |
| WebXR / Immersive AR | `device::mojom::XRDevice` | Deferred indefinitely |

---

## 10. Next Landings

| Phase final | What it delivers |
|-------------|-----------------|
| **Phase 1 final** | CPU + Vulkan backends wired; `SkSurface::makeRasterN32Premul` returns real pixel buffer; `SkCanvas` ops actually rasterise |
| **Phase 3 final** | HarfBuzz text shaper integration; `drawTextBlob` with real glyph positions; Arabic/CJK/Hebrew bidi; variable font support |
| **Phase 6 final** | `SurfaceAggregator` produces merged `CompositorRenderPassDrawQuad`; `viz::Display` drives real swap chain |
| **Phase 8 final** | `compare_pictures` replaced with real CPU raster + per-pixel delta; reference PNGs captured from headless Chromium 124; CI gate: ≤1% mismatched pixels per scene |
