# Breakout Milestone Captures (G3.3, capture-backed)

> Writes PPM frames at menu / mid-play / brick-hit before+after / game-over

<!-- sdn-diagram:id=breakout_captures_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=breakout_captures_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

breakout_captures_spec -> std
breakout_captures_spec -> common
breakout_captures_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=breakout_captures_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Breakout Milestone Captures (G3.3, capture-backed)

Writes PPM frames at menu / mid-play / brick-hit before+after / game-over

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | W5b, G3.3 |
| Category | Testing \| Runtime \| Game2D |
| Status | Active |
| Requirements | doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G3.3) |
| Design | src/app/game.breakout/game.spl |
| Source | `test/03_system/game2d/breakout_captures_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Writes PPM frames at menu / mid-play / brick-hit before+after / game-over
under `build/game2d-breakout/`, with pixel oracles: the struck brick's own
pixel is non-background before the hit and background after (collision
response visible in the framebuffer, not just in game state).

Separate file from breakout_production_spec.spl: uses 160x120 software
captures so the brick-hit pixel oracle fits CI; the separate rendered-oracle
spec records the 800x600 JIT/render performance gap. Run with
`bin/simple test --no-session-daemon <this file> --timeout 900`.

## Scenarios

### Breakout milestone captures (G3.3)

#### captures menu, mid-play, brick-hit before/after, and game-over PPMs

- var backend = HeadlessBackend create
- var app = Game new game
- var driver = LoopDriver new
- render only
- assert true
- step once
- assert equal
- render only
- assert true
- assert true
- render only
- assert true
-
- assert not equal
- step once
- assert true
- assert false
- assert true
- assert equal
- step once
- assert equal
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = HeadlessBackend.create(CAPTURE_W, CAPTURE_H)
var app = Game.new_game()
var driver = LoopDriver.new(60)

# Menu
render_only(backend, app)
assert_true(capture_ppm(backend, "01_menu"))

# Start -> Playing, then stage a ball just above a live brick.
step_once(driver, app, backend, start_snap())
assert_equal(app.state, GameState.Playing)
render_only(backend, app)
assert_true(capture_ppm(backend, "02_mid_play"))

val target = app.bricks[0]
assert_true(target.alive)
app.ball_x = target.x + target.w / 2.0
app.ball_y = target.y + target.h + 6.0
app.ball_vx = 0.0
app.ball_vy = -220.0
val score_before = app.score
render_only(backend, app)
assert_true(capture_ppm(backend, "03_brick_before"))
# Pixel oracle: the brick's own pixel is non-background before the hit.
val brick_px = (target.y as i64 + target.h as i64 / 2) * backend.width +
                (target.x as i64 + target.w as i64 / 2)
val pixel_before = backend.fb[brick_px]
val background_pixel = backend.fb[0]
assert_not_equal(pixel_before, background_pixel)

step_once(driver, app, backend, empty_snap())
assert_true(capture_ppm(backend, "04_brick_after"))
assert_false(app.bricks[0].alive)
assert_true(app.score > score_before)
# Same pixel now reads as background — collision response visible in
# the captured framebuffer, not just in game-state fields.
val pixel_after = backend.fb[brick_px]
assert_equal(pixel_after, backend.fb[0])
print "brick_hit_score_before={score_before} brick_hit_score_after={app.score}"
print "brick_pixel_before={pixel_before} brick_pixel_after={pixel_after}"

# Force a life-loss -> GameOver: 1 life left, ball already past paddle.
app.lives = 1
app.ball_x = 400.0
app.ball_y = 650.0
app.ball_vy = 50.0
step_once(driver, app, backend, empty_snap())
assert_equal(app.state, GameState.GameOver)
assert_true(capture_ppm(backend, "05_game_over"))
print "game_over_score={app.score} game_over_state={app.state}"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G3.3)](doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G3.3))
- **Design:** [src/app/game.breakout/game.spl](src/app/game.breakout/game.spl)


</details>
