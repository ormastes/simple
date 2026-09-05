# Rolling Ball — playable 3D game production proof (capture-backed)

> Runtime (non-grep) system spec for the rolling-ball 3D game. Drives the same PhysicsWorld3D + engine3d CPU render path the game uses, offscreen (no display):

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rolling Ball — playable 3D game production proof (capture-backed)

Runtime (non-grep) system spec for the rolling-ball 3D game. Drives the same PhysicsWorld3D + engine3d CPU render path the game uses, offscreen (no display):

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | W6d, G4.2, G4.3 |
| Category | Testing \| Runtime \| GUI (3D) |
| Status | In Progress |
| Requirements | doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (W6d) |
| Design | src/app/game.rollball/game.spl |
| Source | `test/03_system/game3d/rollball_production_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Runtime (non-grep) system spec for the rolling-ball 3D game. Drives the same
PhysicsWorld3D + engine3d CPU render path the game uses, offscreen (no display):

1. **Win path** — a scripted forward-drive autopilot reaches the goal zone
   (ball center x >= 9), proving the win condition is reachable.
2. **Lose path** — a scripted edge-steer autopilot pushes the ball off the
   course (y drops below the fall threshold), a terminal state distinct from win.
3. **Depth occlusion (G4.3)** — a near obstacle box occludes a far ball marker;
   the overlap pixel reads the obstacle color, not the ball behind it.
4. **Object motion (G4.3)** — under a fixed camera the ball's screen centroid
   moves as it rolls down the lane.
5. **Event handling (production)** — drive/steer input changes the physics
   trajectory against an independent no-input baseline; a scripted camera-pan
   input changes the rendered frame (with an identical-eye negative control);
   input arriving during a terminal (Win) state is neutralized by the pin
   logic without crash or NaN.
6. **Animation (production)** — fixed-timestep physics is deterministic across
   two independent runs; the ball's screen centroid advances monotonically
   left-to-right across start/mid/late captures with absolute pixel bounds;
   consecutive frames differ during motion while a stationary scene re-renders
   pixel-identical (negative control); the HUD bar+text composites over the 3D
   frame without disturbing pixels below the bar.

Sessions here are short (a few hundred fixed steps, no per-frame PPM dump) so the
spec stays fast; the full 60-second endurance session, camera-motion pair, HUD
composite, Vulkan leg, and 800x600 frame-time p95 live in the capture driver
`src/app/game.rollball/game.spl` and its check script
`scripts/check/check-game3d-rollball.shs`.

## Related Specifications

- [game2d_event_replay_spec.spl](../game2d/game2d_event_replay_spec.spl) — 2D replay/animation contract

## Scenarios

### Rolling Ball 3D — win/lose reachability (W6d/G4.2)

#### win-path autopilot reaches the goal zone (x >= 9)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- win-path autopilot reaches the goal zone (x >= 9)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("win-path autopilot reaches the goal zone (x >= 9)")
val fp = run_short("win", 1200)
assert_true(fp[0] >= GOAL_X)
assert_true(fp[1] > FALL_Y)
```

</details>

#### lose-path autopilot drives the ball off the course (falls)

- lose-path autopilot drives the ball off the course (falls)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lose-path autopilot drives the ball off the course (falls)")
val fp = run_short("lose", 1200)
assert_true(fp[1] < FALL_Y)
```

</details>

#### win and lose land in distinct final positions

- win and lose land in distinct final positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("win and lose land in distinct final positions")
val w = run_short("win", 1200)
val l = run_short("lose", 1200)
assert_true(w[0] >= GOAL_X)
assert_true(l[1] < FALL_Y)
```

</details>

### Rolling Ball 3D — capture-backed render proofs (W6d/G4.3)

#### near obstacle occludes far ball (depth test)

- near obstacle occludes far ball (depth test)


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("near obstacle occludes far ball (depth test)")
assert_equal(occlusion_center(), OBST_COLOR)
```

</details>

### Rolling Ball 3D — event handling (production)

#### drive and steer input change the physics trajectory vs a no-input baseline

- drive and steer input change the physics trajectory vs a no-input baseline
- Run an independent 240-step session with NO input (baseline)
- Baseline ball settles on the floor at the start line (absolute oracle)
- Run an independent 240-step session with forward-drive input
- Drive input moved the ball at least 4 units toward the goal
- Run an independent 240-step session with lateral steer input
- Steer input pushed the ball off the lane center in +z


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("drive and steer input change the physics trajectory vs a no-input baseline")
step("Run an independent 240-step session with NO input (baseline)")
val base = run_scripted(false, false, 240)
step("Baseline ball settles on the floor at the start line (absolute oracle)")
assert_true(abs_f(base[0] - (-9.0)) < 0.1)
assert_true(abs_f(base[2]) < 0.1)
assert_true(base[1] > FALL_Y)
step("Run an independent 240-step session with forward-drive input")
val driven = run_scripted(true, false, 240)
step("Drive input moved the ball at least 4 units toward the goal")
assert_true(driven[0] > -5.0)
assert_true(driven[0] - base[0] > 4.0)
step("Run an independent 240-step session with lateral steer input")
val steered = run_scripted(false, true, 240)
step("Steer input pushed the ball off the lane center in +z")
assert_true(steered[2] > 1.0)
assert_true(abs_f(base[2]) < 0.1)
```

</details>

#### scripted camera-pan input changes the rendered frame (with negative control)

- scripted camera-pan input changes the rendered frame (with negative control)
- Render the course from the base follow-camera eye
- Apply the scripted pan input: eye shifts +8 in x, same look target
- Pan changed a substantial pixel count
- Negative control: identical eye re-renders pixel-identical


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("scripted camera-pan input changes the rendered frame (with negative control)")
var e = Engine3D.create(RW, RH)
step("Render the course from the base follow-camera eye")
val base = render_frame(e, 0.0, 1.0, 0.0, -3.0, 4.5, 9.0, 0.0, 1.0, 0.0)
step("Apply the scripted pan input: eye shifts +8 in x, same look target")
val panned = render_frame(e, 0.0, 1.0, 0.0, 5.0, 4.5, 9.0, 0.0, 1.0, 0.0)
step("Pan changed a substantial pixel count")
val nd = diff_count(base, panned, RW * RH)
assert_true(nd > 100)
step("Negative control: identical eye re-renders pixel-identical")
val base2 = render_frame(e, 0.0, 1.0, 0.0, -3.0, 4.5, 9.0, 0.0, 1.0, 0.0)
assert_equal(diff_count(base, base2, RW * RH), 0)
```

</details>

#### input arriving during a terminal (Win) state is neutralized without crash or NaN

- input arriving during a terminal (Win) state is neutralized without crash or NaN
- Drive an independent session until the Win state latches, then keep stepping 240 frames while input events keep arriving; the game's terminal pin runs each frame
- The session actually reached Win before the input storm
- Terminal pose survives the input storm: finite, NaN-free, exactly pinned
- Pinned pose is the winning pose (past the goal line, on the course)


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("input arriving during a terminal (Win) state is neutralized without crash or NaN")
step("Drive an independent session until the Win state latches, then keep stepping 240 frames while input events keep arriving; the game's terminal pin runs each frame")
val r = run_win_then_terminal_input()
step("The session actually reached Win before the input storm")
assert_equal(r[0], 1.0)
step("Terminal pose survives the input storm: finite, NaN-free, exactly pinned")
assert_true(is_finite_f(r[4]))
assert_true(is_finite_f(r[5]))
assert_true(is_finite_f(r[6]))
assert_equal(r[4], r[1])
assert_equal(r[5], r[2])
assert_equal(r[6], r[3])
step("Pinned pose is the winning pose (past the goal line, on the course)")
assert_true(r[1] >= GOAL_X)
assert_true(r[2] > FALL_Y)
```

</details>

### Rolling Ball 3D — animation (production)

#### fixed-timestep physics is deterministic across two independent runs

- fixed-timestep physics is deterministic across two independent runs
- Run the same 300-step drive script in two independently built worlds
- Positions at step 300 are bit-identical
- And the run actually moved (not a frozen-world false green)


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fixed-timestep physics is deterministic across two independent runs")
step("Run the same 300-step drive script in two independently built worlds")
val a = run_scripted(true, false, 300)
val b = run_scripted(true, false, 300)
step("Positions at step 300 are bit-identical")
assert_equal(a[0], b[0])
assert_equal(a[1], b[1])
assert_equal(a[2], b[2])
step("And the run actually moved (not a frozen-world false green)")
assert_true(a[0] > -5.0)
```

</details>

#### ball centroid advances monotonically across start/mid/late frames (fixed camera)

- ball centroid advances monotonically across start/mid/late frames (fixed camera)
- Drive one session, snapshotting ball positions at steps 20, 140, 260
- Render the three snapshots under one fixed camera (eye 0,9,16)
- Ball visible in every frame; centroid x strictly increases with margin
- Absolute screen bounds: start left of center, late right of center


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ball centroid advances monotonically across start/mid/late frames (fixed camera)")
step("Drive one session, snapshotting ball positions at steps 20, 140, 260")
val ps = win_snapshots()
step("Render the three snapshots under one fixed camera (eye 0,9,16)")
var e = Engine3D.create(RW, RH)
val f0 = render_frame(e, ps[0], ps[1], ps[2], 0.0, 9.0, 16.0, 0.0, 1.0, 0.0)
val f1 = render_frame(e, ps[3], ps[4], ps[5], 0.0, 9.0, 16.0, 0.0, 1.0, 0.0)
val f2 = render_frame(e, ps[6], ps[7], ps[8], 0.0, 9.0, 16.0, 0.0, 1.0, 0.0)
dump_ppm("build/game3d-rollball/spec_anim_start.ppm", f0)
dump_ppm("build/game3d-rollball/spec_anim_mid.ppm", f1)
dump_ppm("build/game3d-rollball/spec_anim_late.ppm", f2)
step("Ball visible in every frame; centroid x strictly increases with margin")
val c0 = find_centroid(f0, RW, RH, BALL_COLOR)
val c1 = find_centroid(f1, RW, RH, BALL_COLOR)
val c2 = find_centroid(f2, RW, RH, BALL_COLOR)
assert_true(c0[2] > 0)
assert_true(c1[2] > 0)
assert_true(c2[2] > 0)
assert_true(c1[0] > c0[0] + 3)
assert_true(c2[0] > c1[0] + 3)
step("Absolute screen bounds: start left of center, late right of center")
assert_true(c0[0] < 80)
assert_true(c2[0] > 80)
```

</details>

#### moving scene changes consecutive frames; stationary scene re-renders identical

- moving scene changes consecutive frames; stationary scene re-renders identical
- Advance a driven ball 20 steps between two mid-motion frames
- Frames during motion differ beyond the noise threshold
- Negative control: the same (stationary) pose renders pixel-identical twice


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("moving scene changes consecutive frames; stationary scene re-renders identical")
step("Advance a driven ball 20 steps between two mid-motion frames")
val pa = run_scripted(true, false, 140)
val pb = run_scripted(true, false, 160)
var e = Engine3D.create(RW, RH)
val fa = render_frame(e, pa[0], pa[1], pa[2], 0.0, 9.0, 16.0, 0.0, 1.0, 0.0)
val fb = render_frame(e, pb[0], pb[1], pb[2], 0.0, 9.0, 16.0, 0.0, 1.0, 0.0)
step("Frames during motion differ beyond the noise threshold")
assert_true(diff_count(fa, fb, RW * RH) > 10)
step("Negative control: the same (stationary) pose renders pixel-identical twice")
val fb2 = render_frame(e, pb[0], pb[1], pb[2], 0.0, 9.0, 16.0, 0.0, 1.0, 0.0)
assert_equal(diff_count(fb, fb2, RW * RH), 0)
```

</details>

#### HUD bar and text composite over the 3D frame without disturbing pixels below

- HUD bar and text composite over the 3D frame without disturbing pixels below
- Render a 3D course frame
- Composite the HUD bar + label with the 2D software backend
- HUD bar pixel is opaque HUD background; glyph pixels present
- 3D content below the bar is untouched by the composite


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("HUD bar and text composite over the 3D frame without disturbing pixels below")
step("Render a 3D course frame")
var e = Engine3D.create(RW, RH)
val frame = render_frame(e, 0.0, 1.0, 0.0, -3.0, 4.5, 9.0, 0.0, 1.0, 0.0)
step("Composite the HUD bar + label with the 2D software backend")
var b = SoftwareBackend.create()
assert_true(b.init(RW, RH))
b.draw_image(0, 0, RW, RH, frame)
b.draw_rect_filled(0, 0, RW, 14, HUD_BG)
b.draw_text(3, 4, "TIME 4.3s WIN", HUD_FG, 6)
val hud = b.read_pixels()
dump_ppm("build/game3d-rollball/spec_hud.ppm", hud)
step("HUD bar pixel is opaque HUD background; glyph pixels present")
assert_equal(hud[2 * RW + 2], HUD_BG)
var white = 0
var hy = 0
while hy < 14:
    var hx = 0
    while hx < RW:
        if hud[hy * RW + hx] == HUD_FG:
            white = white + 1
        hx = hx + 1
    hy = hy + 1
assert_true(white > 0)
step("3D content below the bar is untouched by the composite")
assert_equal(hud[60 * RW + 80], frame[60 * RW + 80])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (W6d)`
- **Design:** `src/app/game.rollball/game.spl`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5e96a081757191cd6ca6b1d599594e9d93f4c839742fca7fd560596f58e871ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e96a081757191cd6ca6b1d599594e9d93f4c839742fca7fd560596f58e871ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e96a081757191cd6ca6b1d599594e9d93f4c839742fca7fd560596f58e871ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/game3d/rollball_production_spec.spl
mirror: doc/06_spec/03_system/game3d/rollball_production_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/game3d/rollball_production_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/game3d/rollball_production_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/game3d/rollball_production_spec.spl:364:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'win-path autopilot reaches the goal zone (x >= 9)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/game3d/rollball_production_spec.spl:371:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lose-path autopilot drives the ball off the course (falls)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/game3d/rollball_production_spec.spl:377:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'win and lose land in distinct final positions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
