# Game Library Extraction — Research TLDR

## Inventory

**Breakout (275 loc):** Game-specific state (Menu/Playing/GameOver), paddle, bricks, score. Hand-rolls AABB collision (lines 156–199) instead of using `engine.physics.collision2d`. Uses game2d.loop.driver ✓, Canvas ✓, InputSnapshot ✓.

**Rollball (583 loc):** Game-specific autopilot, win/lose detection, physics sphere. Hand-rolls 30 lines of utilities: `find_centroid()` (pixel centroid), `diff_count()` (pixel divergence), `dump_ppm()` (P3 PPM dump), `composite_hud()` (HUD overlay), `run_session()` (session harness with frame capture + state pinning). Uses PhysicsWorld3D ✓, Engine3D ✓, SoftwareBackend ✓.

## Duplication & Gaps

```
find_centroid (line 136)  ← pixel oracle for ball screen position       [reusable, 17 lines]
diff_count (line 154)     ← pixel divergence metric                   [reusable, 8 lines]
dump_ppm (line 183)       ← P3 framebuffer dump for evidence          [reusable, 13 lines]
composite_hud (line 173)  ← HUD bar+text overlay on pixel buffer      [reusable, 8 lines]
run_session (line 216)    ← session loop with capture + state-pin     [partially reusable, 91 lines]
```

**Gap:** No third game can be written without copying these utilities from rollball.

## Top 3 Extraction Targets

1. **`std.game2d.render.evidence`** (30 lines): find_centroid, diff_count, dump_ppm — used by Rollball, needed by all future evidence-based games.
2. **`std.gpu.engine2d.render.hud`** (8 lines): composite_hud — overlays text/rect on pixel buffer, used by Rollball, needed for breakout score HUD.
3. **`std.gpu.game3d.session`** (capture pattern): Extract frame-capture + state-pinning loop wrapper; game autopilot remains game-specific.

**Minor fix:** Breakout `lines 156–199` → replace with `collide_aabb_aabb()` from engine.physics.collision2d.

---

```
doc/01_research/app/game_engine/game_library_extraction.md              ← Full inventory
doc/03_plan/app/game_engine/game_library_extraction_plan.md           ← Extraction plan
```
