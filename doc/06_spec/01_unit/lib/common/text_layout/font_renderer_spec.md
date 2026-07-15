# Font Renderer Contract

**Status:** manually synchronized; executable docgen refresh pending
**Executable:** `test/01_unit/lib/common/text_layout/font_renderer_spec.spl`

Forty unit scenarios cover the canonical transient `FontRenderer` material.
Architecture excludes producer-owned GUI/Web/WM/Draw IR/Engine2D/Engine3D
atlas caches; this unit manual covers the renderer contract itself.

## Operator flow

1. Load a live selected face and reject missing SFFI/font state.
2. Prepare bitmap, vector, and shaped runs through one CPU rasterizer path;
   forged environment glyph pixels must not change transient batch material.
3. Accept atlas-composite program v1 with the identity transform.
4. Report an unknown program version or nonidentity transform as unsupported
   and keep their material identities distinct from the accepted v1/identity
   batch.
5. Prove face generation, configuration identity, glyph cache hits/misses,
   dirty rectangles, fallback, shaping, and browser-facing material remain
   coherent.

The executable assertions are authoritative. The vector and bitmap regressions
compare clean and forged-environment `FontRenderBatch` material from fresh
renderers. Regenerate this manual with SPipe docgen when the pure-Simple runner
is available and require zero stubs.
