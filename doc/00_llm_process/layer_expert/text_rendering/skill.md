# Text rendering layer expert

Canonical ownership is semantic GUI/Web/WM `DrawIrComposition` → Engine2D `draw_text` → shared `FontRenderer` → transient `FontRenderBatch`. Engine3D HUD/world is a separate sibling consumer of the same shaping/material owner. `DrawIrGlyphRunPayload` is handle-free; atlases, face handles, caches, UVs, pipelines, buffers, and device resources remain transient/backend-private. Read `doc/04_architecture/lib/text_i18n/utf8_internationalized_text_architecture.md` before changing rendering paths and retain the two open blockers named in the guide.
