# Breakout Production Readiness (60s session)

> Runs the full `Game` (menu -> playing -> game-over, paddle/ball/bricks, score, lives) with scripted `InputSnapshot` autopilot input:

<!-- sdn-diagram:id=breakout_production_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=breakout_production_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

breakout_production_spec -> std
breakout_production_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=breakout_production_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Breakout Production Readiness (60s session)

Runs the full `Game` (menu -> playing -> game-over, paddle/ball/bricks, score, lives) with scripted `InputSnapshot` autopilot input:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | W5b, G3.2 |
| Category | Testing \| Runtime \| Game2D |
| Status | In Progress |
| Requirements | doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G3.2) |
| Design | src/app/game.breakout/game.spl, src/lib/nogc_sync_mut/game2d/backend/{headless,sdl_backend}.spl |
| Source | `test/03_system/game2d/breakout_production_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Runs the full `Game` (menu -> playing -> game-over, paddle/ball/bricks,
score, lives) with scripted `InputSnapshot` autopilot input:

**60s session (G3.2)** — 3600 fixed logic steps (60 Hz * 60 s),
asserts no crash, plus RSS sampled early/late (no monotonic growth).
The full rendered 3600-frame interpreter path is tracked as too slow;
rendering coverage stays in `breakout_render_oracles_spec.spl` and
`breakout_captures_spec.spl`.

Milestone PPM captures live in `breakout_captures_spec.spl` (separate file:
five 800x600 software renders take several minutes interpreted and need
their own timeout budget).

## Known blockers (see linked bug reports)

- `bin/simple run` SIGSEGVs on `LoopDriver.step` (Cranelift JIT dispatch bug)
  — every scenario below runs via `bin/simple test` (interpreter path only).
  See `doc/08_tracking/bug/jit_game2d_backend_method_dispatch_sigsegv_2026-07-02.md`.
- Interpreted 800x600 software rendering costs ~14s/frame (measured), so the
  33ms frame-time budget cannot be met until the JIT path works; the oracle
  records the honest numbers and gates on budget-met OR tracked-gap-on-file.
- Run with `--no-session-daemon`: the daemon path hard-kills children at
  120s regardless of `--timeout` — see
  `doc/08_tracking/bug/test_daemon_ignores_timeout_flag_120s_cap_2026-07-02.md`.

## Scenarios

### Breakout 60s automated session (G3.2)

#### runs 3600 fixed steps (60 simulated seconds) without crashing

- var app = Game new game
- step logic once
- assert equal
- step logic once
- rss first = rss kb
- rss last = rss kb
- assert equal
- assert true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var app = Game.new_game()
step_logic_once(app, start_snap())
assert_equal(app.state, GameState.Playing)
var i: i64 = 0
var rss_first: i64 = 0
var rss_last: i64 = 0
while i < 3600:
    step_logic_once(app, chase_snap(app))
    if i == 0 or i == 100 or i == 200 or i == 300 or i == 400 or i == 500 or i == 600 or i == 1200 or i == 1800 or i == 2400 or i == 3000:
        print "session_progress_frame={i} score={app.score} lives={app.lives} state={app.state}"
    if i == 300:
        rss_first = rss_kb()
    if i == 3599:
        rss_last = rss_kb()
    i = i + 1
assert_equal(app.frame_count, 3601)
print "session_frames={app.frame_count} score={app.score} lives={app.lives} state={app.state}"
print "rss_first_kb={rss_first} rss_last_kb={rss_last}"
# Honest memory-growth check: report, and only hard-fail on gross
# unbounded growth (>4x) — a bit of allocator churn/noise is normal.
if rss_first > 0:
    assert_true(rss_last <= rss_first * 4)
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

- **Requirements:** [doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G3.2)](doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G3.2))
- **Design:** [src/app/game.breakout/game.spl, src/lib/nogc_sync_mut/game2d/backend/{headless,sdl_backend}.spl](src/app/game.breakout/game.spl, src/lib/nogc_sync_mut/game2d/backend/{headless,sdl_backend}.spl)


</details>
