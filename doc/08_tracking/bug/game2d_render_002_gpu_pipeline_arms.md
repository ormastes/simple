# GAME-RENDER-002: GPU/SDL pipeline arms for new RenderCommand variants

**Priority:** medium (headless path is unblocked; live-window text/outlined-shapes won't render until done)
**Filed:** 2026-04-25
**Code:** GAME-RENDER-002
**Component:** `engine/render/{batch,pipeline,gpu_pipeline}.spl`
**Discovered by:** game2d-framework SStack Phase 5 implement / Phase 7 verification

## Description

`std.game2d` Phase-5 added three new `RenderCommand` variants to
`src/lib/nogc_sync_mut/engine/render/command.spl`:

- `DrawText { string, x, y, style, color, z }`
- `DrawRectOutlined { rect, color }`
- `DrawCircleOutlined { center, radius, color }`

The headless `SoftwareRenderer` (`engine/render/pipeline.spl`) handles all three
correctly — `game2d_golden_spec.spl` (11/11) and `game2d_replay_spec.spl` (10/10)
prove it.

The **live GPU/SDL pipeline arms** in `engine/render/{batch.spl,
gpu_pipeline.spl}` and the live branch of `engine/render/pipeline.spl` carry
TODO stubs tagged `GAME-RENDER-002` for the same three variants. The windowed
demo (`bin/simple game run`) draws sprites and filled shapes correctly, but
text and outlined shapes are no-ops on the live path.

## Evidence

- `src/lib/nogc_sync_mut/engine/render/batch.spl` — TODO arms for the 3 new variants.
- `src/lib/nogc_sync_mut/engine/render/pipeline.spl` — live-branch arms TODO.
- `src/lib/nogc_sync_mut/engine/render/gpu_pipeline.spl` — same.
- `.sstack/game2d-framework/state.md` `### 7-verify-rerun-2 W4` item 2: "GAME-RENDER-002 GPU/SDL pipeline arms".

## Suggested fix direction

1. `DrawRectOutlined` / `DrawCircleOutlined` — straightforward in the live path;
   reuse the existing fill-arm geometry generation, change primitive topology
   (line strip / line loop) and stride.
2. `DrawText` — wire `engine/render/text.spl::render_text_to_buffer()`
   (already used in headless `SoftwareRenderer`) into the live present path,
   or upload the rasterized glyph atlas as a texture and render via existing
   sprite arm.

The headless contract is the source of truth — copy parameter handling from
`SoftwareRenderer.execute_*` arms.

## Partial Resolution 2026-04-25

**Status:** PARTIAL — software pipeline rect+circle outlined arms implemented;
GPU pipeline + DrawText still amber.

**Implemented (`engine/render/pipeline.spl`):**
- `DrawRectOutlined` — both `_process_command` and
  `_process_command_with_textures` arms now call new
  `_rasterize_rect_outlined()` helper, which emits 4 `_rasterize_line` calls
  (top/right/bottom/left) at width=1.0.
- `DrawCircleOutlined` — both arms now call new `_rasterize_circle_outlined()`
  helper, a Bresenham midpoint-circle algorithm plotting 8 octants per
  iteration via `set_pixel`. Pure integer arithmetic, no `>>` ops.

**Deferred (still amber):**
- `DrawText` arm in software pipeline (lines 160 + 353) — needs glyph atlas
  / wiring to `engine/render/text.spl::render_text_to_buffer`.
  Out-of-scope: would require reading and integrating an existing 5x7 stub or
  vendoring a font.
- `gpu_pipeline.spl` arms for `DrawRectOutlined` / `DrawCircleOutlined` /
  `DrawText` — all three need GPU vertex-buffer construction + line-topology
  passes, which the existing GPU pipeline does not yet emit. Per sprint scope
  rule "Acceptable to leave the GPU arms as TODO and only implement the
  `gpu_pipeline.spl` arms that map to existing primitives", deferred entirely.

**Verification:** All 9 game2d specs remain 122/122 green. `canvas_api_spec`
(14/14) exercises the methods that emit these commands; `golden_spec` (11/11)
exercises the headless rasterization path that the new helpers feed.
