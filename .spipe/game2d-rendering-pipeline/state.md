# game2d-rendering-pipeline — State

## Status: complete

## Goal
Implement the Game2D rendering pipeline: sprite batch rendering, texture atlas (2D),
and draw call batching in `src/lib/nogc_sync_mut/game2d/render/`.

## Scope
- `src/lib/nogc_sync_mut/game2d/render/sprite_batch.spl` — SpriteBatch: groups DrawSprite commands by texture_id to minimize GPU draw calls
- `src/lib/nogc_sync_mut/game2d/render/texture_atlas.spl` — TextureAtlas2D: 2D-layer shelf-pack atlas (wraps game2d Image/TextureId, separate from engine3d atlas)
- `src/lib/nogc_sync_mut/game2d/render/draw_batcher.spl` — DrawBatcher: state machine that collects commands into batches, flushes on texture-break
- `src/lib/nogc_sync_mut/game2d/render/__init__.spl` — updated to re-export new types

## Existing infrastructure reused
- `engine/render/batch.spl` — z-order sort (`sort_commands_by_z`)
- `engine/render/command.spl` — `RenderCommand`, `RenderCommandBuffer`, `TextureId`, `Rect2`, `Vec2`, `ZIndex`
- `engine/render/texture_atlas3d.spl` — shelf-pack algorithm reference (not imported; 2D variant reimplemented)
- `engine/render/sprite_animation.spl` — `AnimationFrame` for sprite sheet addressing
- `game2d/render/canvas.spl` — Canvas/Image/Font usage patterns
- `game2d/render/image.spl` — `Image`, `RenderError`

## Architecture decisions
- MDSOC: each file is a single responsibility module
- No inheritance: composition only
- game2d layer stays in `nogc_sync_mut` (no gc/async required for batching)
- `SpriteBatch` holds a `[SpriteEntry]` list and flushes to a `RenderCommandBuffer`
- `TextureAtlas2D` uses pixel-coord shelf pack; normalized UVs computed on lookup
- `DrawBatcher` sorts by (texture_id, z_order) then emits contiguous DrawSprite runs

## Completed
- [x] state.md
- [x] texture_atlas.spl
- [x] sprite_batch.spl
- [x] draw_batcher.spl
- [x] __init__.spl updated

## Notes
- `game2d/app/app.spl` `pass_do_nothing` bodies are intentional trait-default no-ops (per design).
  Concrete games override only what they need. `app/run.spl` and `loop/driver.spl` provide
  the full game loop and init/update/render cycle — no changes needed to the app layer.
