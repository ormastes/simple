# Game Library Extraction Plan

**Date:** 2026-07-03 | **Scope:** Extraction + First Consumer Adoption | **No Implementation**

## Strategy: Smallest Extraction

Three independent library additions with games as first consumers. No framework invention; only code that appears twice or every future game will need.

### 1. Evidence Pixel Oracles — `std.game2d.render.evidence`

**Source:** Rollball `src/app/game.rollball/game.spl:136–195`

**Functions to extract:**
```
find_centroid(pixels: [u32], w: i32, h: i32, color: u32) -> [i64]
  Returns [cx, cy, count] — center-of-mass for all pixels matching color.
  Lines 136–152 (17 lines, pure function).

diff_count(a: [u32], b: [u32], n: i32) -> i64
  Count differing pixels between framebuffers.
  Lines 154–161 (8 lines, pure function).

dump_ppm(path: text, pixels: [u32], w: i32, h: i32) -> bool
  Write P3 PPM format framebuffer to disk.
  Lines 183–195 (13 lines).
```

**Adoption strategy:**
- Rollball imports from `std.game2d.render.evidence` instead of defining inline (12 callsites update)
- Breakout test suite (`test/03_system/game2d/breakout_render_oracles_spec.spl`) gains direct import for future evidence modes
- Third game gains zero-copy evidence harness

**Behavior preservation:** All three games use identical logic (no game-specific tuning in find_centroid/diff_count).

**Test bed:** Rollball's existing `MOTION`, `DISTINCT`, `OCCLUSION` gates validate centroid + diff behavior (lines 519–541).

---

### 2. HUD Compositing — `std.gpu.engine2d.render.hud`

**Source:** Rollball `src/app/game.rollball/game.spl:173–180`

**Function to extract:**
```
composite_hud(pixels3d: [u32], w: i32, h: i32, label: text) -> [u32]
  Overlay SoftwareBackend rect (dark bar) + text at top of pixel buffer.
  Lines 173–180 (8 lines).
  Depends on: SoftwareBackend.create(), draw_rect_filled(), draw_text(), read_pixels().
```

**Adoption strategy:**
- Rollball imports from `std.gpu.engine2d.render.hud` (1 callsite update, line 549)
- Breakout will use for `draw()` -> HUD text compositing when evidence mode is enabled
- Third game reuses without duplication

**Behavior preservation:** Hardcoded colors (HUD_BG=0xFF101018, HUD_FG=0xFFFFFFFF) → parameters in extracted version.

**Test bed:** Rollball's `HUD` gate validates overlay (lines 547–563): checks bar background + glyph pixel count.

---

### 3. Session Harness — `std.gpu.game3d.session`

**Source:** Rollball `src/app/game.rollball/game.spl:216–306`

**Pattern to extract:**
```
struct SessionCapture:
  start_frame: [u32]
  mid_frame: [u32]
  near_frame: [u32]
  end_frame: [u32]
  motion_a: [u32]         — fixed camera, early motion
  motion_b: [u32]         — fixed camera, late motion

fn run_fixed_session(world: PhysicsWorld3D, ball: NodeId, bi: i64,
                      e: Engine3D, dt: f64, steps: i64,
                      render_fn: (e: Engine3D, step: i64) -> [u32],
                      state_fn: (world, step: i64) -> GameState) -> SessionCapture
  Generic session loop: pump world.step(dt), check state_fn for terminal,
  pin pose on terminal, sample frames via render_fn at key steps (20, 140, end).
```

**Adoption strategy:**
- Rollball: Extract run_session's loop skeleton + capture pattern (lines 230–306)
- Game autopilot logic (lines 232–245) remains in Rollball (NOT in library)
- Library function takes closures for autopilot injection + render + state check
- Breakout does not adopt (2D; uses LoopDriver.step instead)

**Behavior preservation:** Library loop is identical to current Rollball loop; only render_fn + state_fn change per game.

**Test bed:** Rollball's existing `SESSION`, `WINSTATE`, `LOSESTATE` gates validate fixed-step determinism (lines 499–515).

---

### 4. Minor Fix: Breakout AABB Collision

**Source:** Breakout `src/app/game.breakout/game.spl:156–199`

**Change:** Replace hand-rolled AABB checks with `engine.physics.collision2d` calls.

**Callsites (3 methods):**
- `_update_ball_walls()` (lines 156–165): Simple bounce — no collision2d needed (wall planes are trivial)
- `_update_ball_paddle()` (lines 167–178): Check ball-rect overlap — use `collide_circle_aabb()` (line 172)
- `_update_ball_bricks()` (lines 180–199): Check ball-rect overlap — use `collide_circle_aabb()` in loop (line 187)

**Impact:** Lines of change: ≤ 2 (import collision2d; replace overlap checks). No behavior change — same AABB checks, same collision response.

**Test bed:** `test/03_system/game2d/breakout_production_spec.spl` validates game-over conditions (all 32 bricks can be destroyed; lives decrement on miss).

---

## BDD: Behavior Preservation via Tests

No new tests; existing suites validate extraction correctness.

**Rollball:**
- `test/03_system/game3d/rollball_production_spec.spl`: Gates SESSION, WINSTATE, LOSESTATE, MOTION, DISTINCT, OCCLUSION, CAMERA, HUD, VULKAN, PERF
  - Same gates post-extraction: all pass if extract code identical
- Evidence oracle gates (MOTION, DISTINCT, OCCLUSION) prove find_centroid/diff_count correctness
- HUD gate proves composite_hud correctness

**Breakout:**
- `test/03_system/game2d/breakout_production_spec.spl`: Game logic gates (score, lives, win, lose)
- `test/03_system/game2d/breakout_render_oracles_spec.spl`: Frame hash + divergence (no change; optional future use of evidence module)
- `test/03_system/physics_breakout_spec.spl`: Game physics gates

All tests stay green post-extraction (same code, new location).

---

## Deliverables

1. Create `src/lib/game2d/render/evidence.spl` with find_centroid, diff_count, dump_ppm
2. Create `src/lib/gpu/engine2d/render/hud.spl` with composite_hud signature + SoftwareBackend wrapper
3. Create `src/lib/gpu/game3d/session.spl` with run_fixed_session harness + SessionCapture struct
4. Update Rollball imports: 1 + 1 + 1 = 3 import statements
5. Optional: Update Breakout to use collision2d (2 imports + 1 loop change)
6. Verify: `bin/simple test` — all game tests pass unchanged

---

## Effort

- **Per library:** ~15 min (copy + signature adjustment)
- **Per game adoption:** ~5 min (update imports + callsites)
- **Breakout collision fix:** ~10 min
- **Total:** ~1 hour (no new logic, extraction-only)
