# Game Library Extraction Research

**Status:** Research Phase | **Date:** 2026-07-03 | **Phase:** Inventory & Gap Analysis

## Executive Summary

The two shipped games (Breakout 2D, Rollball 3D) each hand-roll harness utilities for evidence collection, HUD compositing, and deterministic replay that belong in reusable libraries. Rollball creates 30 lines of pixel oracle code (find_centroid, diff_count, dump_ppm); both games manually manage state machines and session control. Extraction opportunity: move proven pieces into `std.game2d.render.*` and `std.gpu.game3d.session.*` with games as first consumers, unlocking third-game authorship without code duplication.

## Inventory: Breakout

**File:** `src/app/game.breakout/game.spl` (275 lines) + `main.spl` (54 lines)

### Game-Specific Components
- State machine: `GameState` enum (Menu | Playing | GameOver) — lines 45–48
- Paddle physics: `_update_paddle()` — lines 144–154
- Brick grid: `_spawn_bricks()` — lines 108–121
- Ball-brick collision: `_update_ball_bricks()` — lines 180–199
- Score/lives tracking: `score`, `lives`, `won` fields — lines 84–86

### Hand-Rolled Utilities (Should Reuse Library)
- **AABB collision detection:** Lines 156–199 manually check sphere-to-rect overlap instead of calling `std.nogc_sync_mut.engine.physics.collision2d::collide_aabb_aabb()` or `collide_circle_aabb()`.
  - *Library exists:* Yes, `collision2d.spl` provides `collide_aabb_aabb(pos, hw, hh, …) -> Option<Contact2D>`
  - *Current use:* Zero — all collision is inline (ball-walls, ball-paddle, ball-bricks)

### Library Usage (Correct)
- **LoopDriver:** `main.spl:26` — `LoopDriver.new(60)` for fixed-step accumulator ✓
- **Canvas:** `main.spl:16` + `game.spl:240–274` — rendering via Canvas.rect/circle/text ✓
- **InputSnapshot:** `main.spl:20,32` — input snapshotting for determinism ✓
- **Game2D App trait:** Structural match (load/update/fixed_update/draw) without declared inheritance ✓

### Evidence & Testing Pattern (Not Yet Extracted)
- `test/03_system/game2d/breakout_render_oracles_spec.spl`: Uses frame_hash() and app-state divergence testing (lines 72–98).
- No PPM dump or centroid oracle yet — would need them for third game or full 800x600 evidence mode.

## Inventory: Rollball

**File:** `src/app/game.rollball/game.spl` (583 lines)

### Game-Specific Components
- Autopilot control: `run_session()` lines 232–245 — forward drive + steering impulses
- Physics state machine: `Playing | Win | Lose` — lines 69–72
- Ball pinning logic: Lines 260–273 — freeze ball when terminal state reached
- Win/lose detection: Lines 251–258 — x-coordinate for goal, y for fall-off

### Hand-Rolled Utilities (Extraction Candidates)

#### 1. Pixel Oracle Functions (Lines 136–195)
- **`find_centroid(pixels, w, h, color) -> [i64]`** (Lines 136–152)
  - Returns `[cx, cy, count]` — center-of-mass for all pixels matching a color
  - Used: Lines 526–527 (motion oracle) — proves ball moved in screen space
  - Reusable: Yes — any game testing object visibility or screen position

- **`diff_count(a, b, n) -> i64`** (Lines 154–161)
  - Counts differing pixels between two framebuffers
  - Used: Line 518 (terminal frame divergence), Line 368 (camera pan divergence)
  - Reusable: Yes — any game verifying visual changes

- **`dump_ppm(path, pixels, w, h) -> bool`** (Lines 183–195)
  - Writes P3 PPM format pixel buffer to disk for manual inspection
  - Used: 10 callsites (lines 341, 366–367, 417, 475, 566–571) — evidence stash
  - Reusable: Yes — breakout will use for 800x600 frame capture

#### 2. HUD Compositing (Lines 173–180)
- **`composite_hud(pixels3d, w, h, label) -> [u32]`** (Lines 173–180)
  - Overlays SoftwareBackend rect + text on top of a 3D pixel buffer
  - Line 549: `composite_hud(win.end_frame, RW, RH, hud_label)`
  - Uses: `SoftwareBackend.create()`, `draw_rect_filled()`, `draw_text()`, `read_pixels()`
  - Reusable: Yes — breakout needs HUD for score overlay; third game will reuse

#### 3. Session Harness (Lines 216–306)
- **`run_session(world, ball, bi, e, mode) -> SessionResult`** (Lines 216–306)
  - Wraps fixed-step loop with:
    - Autopilot impulse injection (lines 232–245)
    - State machine latch (lines 251–258)
    - Terminal pose pinning (lines 260–273)
    - Frame capture at key moments (lines 279–289)
  - Returns `SessionResult` struct (lines 198–211) with start/mid/near/end frames + motion pair frames
  - Pattern: Pairs with `LoopDriver.step()` (game2d.loop.driver) — can be abstracted

### Library Usage (Correct)
- **PhysicsWorld3D:** `main.spl:39` + all physics — proper usage ✓
- **Engine3D:** Lines 29–36, 434, 471, 481 — 3D rendering facade ✓
- **SoftwareBackend:** Lines 174–179 — 2D raster for HUD ✓
- **Fixed-timestep:** Explicit while-loop (lines 230–289) instead of `LoopDriver.step()` — works, but not as abstracted as breakout

### Missing from game2d/game3d Libraries
- No `game2d.render.hud` or `gpu.engine2d.render.hud` for compositing
- No `game2d.render.evidence` for pixel oracles (centroid, diff, PPM)
- No `gpu.game3d.session` wrapper for session/capture pattern
- No generic menu/state-machine pattern library

## Library Gaps

### For Breakout
1. Should use `std.nogc_sync_mut.engine.physics.collision2d::collide_aabb_aabb()` instead of hand-rolling lines 156–199
2. Needs HUD compositing for score/lives overlay (future: evidence mode)

### For Rollball
1. Implicit — all utilities hand-rolled because libraries don't exist yet

### For Third Game (To Be Written)
1. Cannot reuse HUD without copying rollball
2. Cannot emit evidence frames (PPM, centroids, divergence) without copying rollball
3. Must hand-roll session harness or duplicate run_session
4. Must hand-roll menu state machine or duplicate breakout's pattern

## Duplication Map

| Code | Breakout | Rollball | Third Game | Reuse Target |
|------|----------|----------|------------|--------------|
| State machine pattern | ✓ | ✓ | ? | `game2d.state.pattern` (optional) |
| HUD rendering | Manual Canvas.text | `composite_hud()` | ? | `game2d.render.hud` |
| Session loop | `LoopDriver.step()` | Explicit while-loop | ? | `gpu.game3d.session` |
| AABB collision | Hand-rolled | N/A (3D) | ? | Use `engine.physics.collision2d` |
| Frame centroid | None yet | `find_centroid()` | ? | `game2d.render.evidence` |
| Frame diff | None yet | `diff_count()` | ? | `game2d.render.evidence` |
| PPM dump | None yet | `dump_ppm()` | ? | `game2d.render.evidence` |

## Key File References

- **Breakout collision (should not exist):** `src/app/game.breakout/game.spl:156–199` (_update_ball_walls, _update_ball_paddle, _update_ball_bricks)
- **Rollball evidence functions:** `src/app/game.rollball/game.spl:136–195` (find_centroid, diff_count, dump_ppm)
- **Rollball HUD:** `src/app/game.rollball/game.spl:173–180` (composite_hud)
- **Rollball session harness:** `src/app/game.rollball/game.spl:216–306` (run_session)
- **Existing collision library:** `src/lib/nogc_sync_mut/engine/physics/collision2d.spl`
- **Existing loop driver:** `src/lib/nogc_sync_mut/game2d/loop/driver.spl`
- **Existing 2D backend:** `src/lib/nogc_sync_mut/game2d/backend/sdl_backend.spl`, `headless.spl`
- **Existing 3D engine:** `src/lib/gc_async_mut/gpu/game3d/game3d_session.spl`
- **Existing soft raster:** `src/lib/gc_async_mut/gpu/engine2d/backend_software.spl`

## Conclusions

1. **Rollball's pixel utilities (find_centroid, diff_count, dump_ppm) are pure, reusable, and ship zero game logic — ready for extraction.**
2. **HUD compositing (composite_hud) is a thin wrapper around SoftwareBackend + draw primitives — ready for extraction.**
3. **Session harness (run_session) is game-specific in its autopilot logic, but the frame-capture + state-pinning pattern is generalizable.**
4. **Breakout should fix AABB collision usage before extraction — one-line change per call site.**
