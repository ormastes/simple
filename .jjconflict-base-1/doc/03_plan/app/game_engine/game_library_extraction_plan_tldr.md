# Game Library Extraction Plan — TLDR

## Three Independent Extractions (No New Framework)

### 1. Pixel Oracles → `std.game2d.render.evidence`
- **Move:** find_centroid, diff_count, dump_ppm from Rollball (lines 136–195)
- **Adoption:** Rollball imports instead of defining inline; Breakout future evidence tests gain zero-copy
- **Behavior:** Pure functions, zero game logic; Rollball MOTION/DISTINCT/OCCLUSION gates validate
- **Impact:** 12 callsite imports (Rollball); zero new tests

### 2. HUD Compositing → `std.gpu.engine2d.render.hud`
- **Move:** composite_hud from Rollball (lines 173–180); parameterize colors
- **Adoption:** Rollball line 549 + future Breakout score HUD
- **Behavior:** SoftwareBackend wrapper; Rollball HUD gate (lines 547–563) validates
- **Impact:** 2 callsite imports; zero new tests

### 3. Session Harness → `std.gpu.game3d.session`
- **Move:** run_session loop skeleton (lines 230–306); autopilot stays game-specific
- **Adoption:** Rollball only (Breakout uses LoopDriver)
- **Behavior:** Identical loop; render_fn/state_fn closures inject game logic
- **Impact:** 1 import; SESSION/WINSTATE/LOSESTATE gates validate

### 4. Minor: Breakout AABB → Use `engine.physics.collision2d` (lines 156–199)
- **Change:** Replace hand-rolled checks with collide_circle_aabb() calls (2 imports, 2 loop changes)
- **Test:** Breakout production spec validates all game-over conditions
- **Impact:** No behavior change

---

## Behavior Preservation

All existing test gates pass unchanged:
- Rollball: SESSION, WINSTATE, LOSESTATE, MOTION, DISTINCT, OCCLUSION, HUD gates prove extraction correctness
- Breakout: production_spec, render_oracles_spec validate game logic + evidence patterns (existing suite)

No new tests written. Code moves, tests stay green.

---

## Effort

~1 hour: 3×copy+import (15 min each), 1×collision fix (10 min), verify tests (10 min).
