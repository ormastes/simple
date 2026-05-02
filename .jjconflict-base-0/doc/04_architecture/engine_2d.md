# Engine2D QEMU Graphics Core Architecture

## Scope

This document locks the Simple OS/QEMU graphics-core subset of Engine2D. The target is not the full game-engine roadmap; it is the x86_64 guest path that boots in QEMU, paints deterministic 2D primitives, supports WM-facing Simple Web smoke coverage, and supports QMP framebuffer capture.

## Layers

- Mandatory BGA boot entries: `examples/simple_os/arch/x86_64/gui_entry_engine2d_min.spl`, `gui_engine2d_primitives_entry.spl`, and `gui_entry_engine2d.spl`
- VirtIO proof entry: `examples/simple_os/arch/x86_64/gui_entry_engine2d_virtio.spl`
- Engine facade: a freestanding Engine2D-style core in `src/os/compositor/engine2d_baremetal_core.spl`
- Mandatory device path: BGA/std-vga framebuffer initialized by `bga_init_framebuffer`, then pixel writes to the framebuffer scanout
- Proof device path: VirtIO-GPU wrapper initialization and direct-framebuffer backend proof, covered separately from mandatory BGA behavior
- WM Simple Web path: `gui_entry_engine2d.spl` initializes WM service and launcher state, renders Simple Web HTML to pixels, and blits those pixels through `Engine2DBaremetalCore`
- Verification: QEMU serial markers plus QMP `screendump` PPM capture

## Locked Behavior

- The entries must call Engine2D-shaped methods: `clear`, `draw_rect_filled`, `draw_rect`, `draw_line`, `draw_circle_filled`, `draw_circle`, and `present`.
- The QEMU primitive fixture must paint deterministic ARGB colors at the coordinates asserted by `test/system/engine2d_primitives_spec.spl`.
- `gui_entry_engine2d.spl` must emit WM, Simple Web, Engine2D core, and final render markers before the bounded capture window and `TEST PASSED`.
- The named scenario `x64-wm-simple-web-check` must use the BGA/std-vga path with the desktop/browser `2G` memory profile.
- `gui_entry_engine2d_virtio.spl` proves VirtIO-GPU wrapper construction and `[gui-e2d-virtio] render-ready`; it is not the mandatory graphics-core acceptance lane.
- The guest must remain alive after the paint marker so QMP capture cannot race guest exit.
- Baselines are not silently refreshed; `UPDATE_BASELINE=1` remains the intentional refresh path.

## Current Blocker

The broad `std.gc_async_mut.gpu.engine2d.engine.Engine2D` facade pulls host/GPU backend symbols into the freestanding link when its drawing methods are called from the x86_64 entry-closure kernel. A narrow internal core is therefore used for the QEMU graphics-core and WM Simple Web lanes until the compiler/linker can keep the public facade from dragging non-baremetal backends into this target.

The same boundary applies to browser rendering in QEMU: Simple Web may produce pixels, but `browser_backend` and the hosted/full `Engine2D` facade stay out of the freestanding QEMU entry closure.

## std.game2d Layer Architecture (2026-04-25)

A `std.game2d` framework layer sits on top of `engine/`. All new code lives under `src/lib/nogc_sync_mut/game2d/**` (28 files, ~2237 LOC, every file ≤ 260 LOC). The full module tree and rationale is in `.sstack/game2d-framework/state.md` `### 3-arch §A "Final on-disk module tree"`.

**Module sub-trees (final on-disk):**
- `game2d/app/` — `app.spl` (trait `App`), `config.spl` (`GameConfig`), `run.spl` (`g.run` facade)
- `game2d/render/` — `canvas.spl` (Canvas builder over `RenderCommandBuffer`), `image.spl`, `font.spl`
- `game2d/input/` — `snapshot.spl`, `keys.spl`, `api.spl`
- `game2d/backend/` — `trait.spl` (`GameBackend`), `headless.spl`, `sdl_backend.spl`, `frame_hash.spl`
- `game2d/asset/` — `asset_id.spl`, `table.spl`, `loader.spl`, `diagnostic.spl`
- `game2d/config/game_sdn.spl` — `game.sdn` loader
- `game2d/time/det_guard.spl` — runtime determinism guard
- `game2d/loop/driver.spl` — fixed-step `LoopDriver`
- `game2d/math/__init__.spl` — pure re-exports of `engine.Vec2/Rect2/Color/Transform2D` + `enum DrawMode`

**Public API surface (exposed via `import std.game2d as g`):** `App`, `GameConfig`, `run`, `Canvas`, `Image`, `Sound`, `Font`, `Sprite`, `InputSnapshot`, `Key`, `MouseButton`, `Vec2`, `Rect`, `Color`, `Transform2D`, `DrawMode`, `AssetId<T>`, `AssetTable`, `AssetError`, `deterministic`.

**Determinism strategy:** runtime guard via thread-local `deterministic_mode` flag toggled by `g.run(...)` enter/leave_callback bracket. `g.time.now()` and `g.random.rand()` panic with `GAME-DET-001` outside an active callback when the flag is set. Compile-time lint rule deferred (see ticket `game2d_det_lint_rule.md`, code GAME-DET-LINT-001).

**Headless backend + frame_hash:** `HeadlessBackend` produces a software framebuffer `[u32]`; `frame_hash(buf)` computes FNV-1a → `u64` for golden-frame stability tests. `ScriptedInput { frames: [InputSnapshot] }` drives replay specs without OS input.

**SDN integration:** `assets.sdn` declares typed image/sound/font handles → `AssetTable` resolver. Diagnostics:
- `GAME-ASSET-001` — missing asset key
- `GAME-ASSET-002` — wrong type
- `GAME-ASSET-014` — atlas index out of bounds

`game.sdn` carries `window`/`runtime`/`startup` config consumed by `GameConfig`.

**Engine layer touched (4 modified files):**
- `src/lib/nogc_sync_mut/engine/render/command.spl` — added `DrawText` / `DrawRectOutlined` / `DrawCircleOutlined` variants
- `src/lib/nogc_sync_mut/engine/render/{batch,pipeline,gpu_pipeline}.spl` — TODO arms tagged `GAME-RENDER-002` (live GPU/SDL pipeline rendering of new variants — headless path is unblocked)
- `src/lib/gc_async_mut/game2d/sprite.spl` — deprecation header (Phase 8 amber: removable once `batch.spl`/`camera.spl` migrate)

**CLI:** `src/app/game/{main,new,run,test,inspect}.spl` + new `CommandEntry { name: "game" }` row in `src/app/cli/dispatch/table.spl`.

For complete API signatures and per-AC coverage gates, see state file `### 3-arch`.
