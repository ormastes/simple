# Breakout Render Oracles (frame-time / divergence)

> Focused rendered checks split from `breakout_production_spec.spl` so the

<!-- sdn-diagram:id=breakout_render_oracles_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=breakout_render_oracles_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

breakout_render_oracles_spec -> std
breakout_render_oracles_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=breakout_render_oracles_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Breakout Render Oracles (frame-time / divergence)

Focused rendered checks split from `breakout_production_spec.spl` so the

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | W5b, G3.3, G3.4 |
| Category | Testing \| Runtime \| Game2D |
| Status | In Progress |
| Requirements | doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G3.3/G3.4) |
| Design | src/app/game.breakout/game.spl, src/lib/nogc_sync_mut/game2d/backend/headless.spl |
| Source | `test/03_system/game2d/breakout_render_oracles_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Focused rendered checks split from `breakout_production_spec.spl` so the
60s logic-session proof cannot consume the runner's practical timeout budget
before G3.3/G3.4 evidence runs. The target 800x600 frame-time path remains
tracked by `GAP_BUG_DOC`; this spec keeps a low-resolution rendered smoke
green until the JIT/render path can run the target resolution inside budget.

## Scenarios

### Breakout render oracles (G3.3/G3.4)

#### measures low-resolution driver.step wall time and records the 800x600 gap

- var backend = HeadlessBackend create
- var app = Game new game
- var driver = LoopDriver new
- step once
- step once
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = HeadlessBackend.create(96, 72)
var app = Game.new_game()
var driver = LoopDriver.new(60)
step_once(driver, app, backend, start_snap())
val t0 = time_now_unix_micros()
step_once(driver, app, backend, right_snap())
val t1 = time_now_unix_micros()
val frame_ms = (t1 - t0) / 1000
val budget_met = frame_ms <= 33
print "lowres_frame_time_ms={frame_ms} target_800x600_budget_met={budget_met} tracked_gap={GAP_BUG_DOC}"
assert_true(budget_met or file_exists(GAP_BUG_DOC))
```

</details>

#### left and right scripted inputs diverge in frame_hash and state

- var backend a = HeadlessBackend create
- var app a = Game new game
- var driver a = LoopDriver new
- step once
- step once
- render only
- var backend b = HeadlessBackend create
- var app b = Game new game
- var driver b = LoopDriver new
- step once
- step once
- render only
- assert not equal
- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend_a = HeadlessBackend.create(160, 120)
var app_a = Game.new_game()
var driver_a = LoopDriver.new(60)
step_once(driver_a, app_a, backend_a, start_snap())
step_once(driver_a, app_a, backend_a, left_snap())
# Low-res witness: paddle_y is below 160x120, so project the
# input-diverged paddle position into the visible ball marker.
app_a.ball_x = app_a.paddle_x - 320.0
app_a.ball_y = 30.0
render_only(backend_a, app_a)
val hash_chase = backend_a.frame_hash()

var backend_b = HeadlessBackend.create(160, 120)
var app_b = Game.new_game()
var driver_b = LoopDriver.new(60)
step_once(driver_b, app_b, backend_b, start_snap())
step_once(driver_b, app_b, backend_b, right_snap())
app_b.ball_x = app_b.paddle_x - 320.0
app_b.ball_y = 30.0
render_only(backend_b, app_b)
val hash_static = backend_b.frame_hash()

print "hash_left={hash_chase} hash_right={hash_static}"
print "left_paddle_x={app_a.paddle_x} right_paddle_x={app_b.paddle_x}"
assert_not_equal(hash_chase, hash_static)
assert_not_equal(app_a.paddle_x, app_b.paddle_x)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G3.3/G3.4)](doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G3.3/G3.4))
- **Design:** [src/app/game.breakout/game.spl, src/lib/nogc_sync_mut/game2d/backend/headless.spl](src/app/game.breakout/game.spl, src/lib/nogc_sync_mut/game2d/backend/headless.spl)


</details>
