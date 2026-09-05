# Breakout Event Handling & Animation Oracles

> Closes the event-handling and animation gaps left open by `breakout_production_spec.spl` (long-session smoke) and `game2d_event_replay_spec.spl` (frame-hash replay):

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Breakout Event Handling & Animation Oracles

Closes the event-handling and animation gaps left open by `breakout_production_spec.spl` (long-session smoke) and `game2d_event_replay_spec.spl` (frame-hash replay):

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | W5b, G3.2, G3.3 |
| Category | Testing \| Runtime \| Game2D |
| Status | In Progress |
| Requirements | doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G3.2/G3.3) |
| Design | src/app/game.breakout/game.spl, src/lib/nogc_sync_mut/game2d/input/{snapshot,api}.spl |
| Source | `test/03_system/game2d/breakout_event_animation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Closes the event-handling and animation gaps left open by
`breakout_production_spec.spl` (long-session smoke) and
`game2d_event_replay_spec.spl` (frame-hash replay):

- **Event edges** — `key_pressed_this_frame` fires only on a press edge:
  a held key without an edge never starts or restarts the game; ENTER works
  like SPACE; paddle motion is exactly `PADDLE_SPEED * dt` per held frame,
  zero drift with no input, and hard-clamped at both screen edges.
- **Animation / physics** — absolute ball positions on the opening
  trajectory, exact velocity reflection on all three walls, paddle bounce
  with contact-offset deflection, single-brick break with score increment,
  life-loss reset, game-over on last life, win on last brick.
- **Determinism** — two independently produced scripted sessions fold every
  per-step game state into a hash; the hashes must be identical, and a
  different input script must diverge (the hash is proven sensitive).

All oracles read `Game` object state (positions, velocities, score, lives,
brick liveness) — the strongest available oracle — never pixels.
Interpreter-mode friendly: no rendering, no backend, pure `fixed_update`.

## Related Specifications

- [breakout_production_spec.spl](breakout_production_spec.spl) — 60s session smoke
- [game2d_event_replay_spec.spl](game2d_event_replay_spec.spl) — frame-hash replay
- [breakout_captures_spec.spl](breakout_captures_spec.spl) — pixel oracles

## Scenarios

### Breakout event handling (press-edge semantics)

#### held space without a press edge never starts the game

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- held space without a press edge never starts the game
- Feed five frames of SPACE held down but not press-edged
- A real press edge then starts the game exactly once
- Continuing the hold after the edge does not re-trigger a reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("held space without a press edge never starts the game")
var app = Game.new_game()
step("Feed five frames of SPACE held down but not press-edged")
step_logic_n(app, held_snap(SPACE_KEY), 5)
assert_equal(app.state, GameState.Menu)
step("A real press edge then starts the game exactly once")
step_logic_once(app, press_snap(SPACE_KEY))
assert_equal(app.state, GameState.Playing)
step("Continuing the hold after the edge does not re-trigger a reset")
step_logic_n(app, held_snap(SPACE_KEY), 3)
assert_equal(app.state, GameState.Playing)
```

</details>

#### enter press edge starts the game like space

- enter press edge starts the game like space
- Press ENTER on the menu


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enter press edge starts the game like space")
var app = Game.new_game()
step("Press ENTER on the menu")
step_logic_once(app, press_snap(ENTER_KEY))
assert_equal(app.state, GameState.Playing)
assert_equal(app.score, 0)
assert_equal(app.lives, 3)
```

</details>

#### game over restarts only on a fresh press edge and fully resets

- game over restarts only on a fresh press edge and fully resets
- Force the last life to be lost
- SPACE held over from before the game ended does not restart
- A fresh press edge restarts with score, lives, bricks and ball reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("game over restarts only on a fresh press edge and fully resets")
var app = started_game()
step("Force the last life to be lost")
app.lives = 1
app.score = 70
app.ball_y = 650.0
app.ball_vy = 220.0
step_logic_once(app, empty_snap())
assert_equal(app.state, GameState.GameOver)
assert_false(app.won)
assert_equal(app.lives, 0)
step("SPACE held over from before the game ended does not restart")
step_logic_n(app, held_snap(SPACE_KEY), 3)
assert_equal(app.state, GameState.GameOver)
step("A fresh press edge restarts with score, lives, bricks and ball reset")
step_logic_once(app, press_snap(SPACE_KEY))
assert_equal(app.state, GameState.Playing)
assert_equal(app.score, 0)
assert_equal(app.lives, 3)
assert_equal(alive_bricks(app), 32)
assert_equal(app.ball_x, 400.0)
assert_equal(app.ball_y, 551.0)
```

</details>

#### held arrow keys move the paddle exactly speed*dt per step

- held arrow keys move the paddle exactly speed*dt per step
- Hold LEFT for 20 fixed steps
- Hold RIGHT for 40 fixed steps


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("held arrow keys move the paddle exactly speed*dt per step")
var app = started_game()
park_ball(app)
val x0 = app.paddle_x
assert_equal(x0, 350.0)
step("Hold LEFT for 20 fixed steps")
step_logic_n(app, held_snap(LEFT_KEY), 20)
expect(absd(app.paddle_x, x0 - PADDLE_SPEED * 20.0 * DT)).to_be_less_than(EPS)
step("Hold RIGHT for 40 fixed steps")
step_logic_n(app, held_snap(RIGHT_KEY), 40)
expect(absd(app.paddle_x, x0 + PADDLE_SPEED * 20.0 * DT)).to_be_less_than(EPS)
```

</details>

#### no input and opposing inputs cause zero paddle drift

- no input and opposing inputs cause zero paddle drift
- Run 60 fixed steps with no input at all
- Run 60 fixed steps with LEFT and RIGHT held together


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("no input and opposing inputs cause zero paddle drift")
var app = started_game()
park_ball(app)
val x0 = app.paddle_x
step("Run 60 fixed steps with no input at all")
step_logic_n(app, empty_snap(), 60)
assert_equal(app.paddle_x, x0)
step("Run 60 fixed steps with LEFT and RIGHT held together")
val kl = KeyCode(code: LEFT_KEY)
val kr = KeyCode(code: RIGHT_KEY)
val both = InputSnapshot.from_raw([kl, kr], [], Vec2(x: 0.0, y: 0.0), [])
step_logic_n(app, both, 60)
assert_equal(app.paddle_x, x0)
```

</details>

#### paddle clamps exactly at both screen edges

- paddle clamps exactly at both screen edges
- Hold LEFT far longer than needed to reach the wall
- Hold RIGHT far longer than needed to reach the other wall


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("paddle clamps exactly at both screen edges")
var app = started_game()
park_ball(app)
step("Hold LEFT far longer than needed to reach the wall")
step_logic_n(app, held_snap(LEFT_KEY), 120)
assert_equal(app.paddle_x, 0.0)
step("Hold RIGHT far longer than needed to reach the other wall")
step_logic_n(app, held_snap(RIGHT_KEY), 240)
assert_equal(app.paddle_x, 700.0)
```

</details>

### Breakout animation and physics (fixed_update determinism)

#### ball follows the exact opening trajectory

- ball follows the exact opening trajectory
- The start-press frame itself does not advance physics
- After 10 collision-free steps the ball is at the analytic position
- After 30 total steps it is still exactly on the line


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ball follows the exact opening trajectory")
var app = started_game()
step("The start-press frame itself does not advance physics")
assert_equal(app.ball_x, 400.0)
assert_equal(app.ball_y, 551.0)
step("After 10 collision-free steps the ball is at the analytic position")
step_logic_n(app, empty_snap(), 10)
expect(absd(app.ball_x, 400.0 + 140.0 * 10.0 * DT)).to_be_less_than(EPS)
expect(absd(app.ball_y, 551.0 - 220.0 * 10.0 * DT)).to_be_less_than(EPS)
step("After 30 total steps it is still exactly on the line")
step_logic_n(app, empty_snap(), 20)
expect(absd(app.ball_x, 400.0 + 140.0 * 30.0 * DT)).to_be_less_than(EPS)
expect(absd(app.ball_y, 551.0 - 220.0 * 30.0 * DT)).to_be_less_than(EPS)
```

</details>

#### wall bounces reflect velocity exactly on left, right, and top walls

- wall bounces reflect velocity exactly on left, right, and top walls
- Stage the ball just off the left wall moving left
- Stage the ball just off the right wall moving right
- Stage the ball just below the top wall moving up


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wall bounces reflect velocity exactly on left, right, and top walls")
var app = started_game()
step("Stage the ball just off the left wall moving left")
app.ball_x = 8.0
app.ball_y = 300.0
app.ball_vx = -140.0
app.ball_vy = 0.0
step_logic_once(app, empty_snap())
assert_equal(app.ball_vx, 140.0)
assert_equal(app.ball_x, 7.0)
step("Stage the ball just off the right wall moving right")
app.ball_x = 792.0
app.ball_vx = 140.0
step_logic_once(app, empty_snap())
assert_equal(app.ball_vx, -140.0)
assert_equal(app.ball_x, 793.0)
step("Stage the ball just below the top wall moving up")
app.ball_x = 400.0
app.ball_y = 8.0
app.ball_vx = 0.0
app.ball_vy = -220.0
step_logic_once(app, empty_snap())
assert_equal(app.ball_vy, 220.0)
assert_equal(app.ball_y, 7.0)
```

</details>

#### paddle bounce reflects vy and deflects vx by contact offset

- paddle bounce reflects vy and deflects vx by contact offset
- Drop the ball straight onto the paddle center
- Drop the ball halfway between center and right paddle edge


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("paddle bounce reflects vy and deflects vx by contact offset")
var app = started_game()
step("Drop the ball straight onto the paddle center")
app.ball_x = 400.0
app.ball_y = 550.0
app.ball_vx = 0.0
app.ball_vy = 220.0
step_logic_once(app, empty_snap())
assert_equal(app.ball_vy, -220.0)
assert_equal(app.ball_vx, 0.0)
assert_equal(app.ball_y, 553.0)
step("Drop the ball halfway between center and right paddle edge")
app.ball_x = 425.0
app.ball_y = 550.0
app.ball_vx = 0.0
app.ball_vy = 220.0
step_logic_once(app, empty_snap())
assert_equal(app.ball_vy, -220.0)
assert_equal(app.ball_vx, 130.0)
```

</details>

#### brick break removes exactly one brick and scores exactly 10

- brick break removes exactly one brick and scores exactly 10
- Stage the ball rising into the first brick of the top row
- Exactly one brick died even though the ball grazed the row below


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("brick break removes exactly one brick and scores exactly 10")
var app = started_game()
step("Stage the ball rising into the first brick of the top row")
val target = app.bricks[0]
assert_true(target.alive)
app.ball_x = target.x + target.w / 2.0
app.ball_y = target.y + target.h + 6.0
app.ball_vx = 0.0
app.ball_vy = -220.0
step_logic_once(app, empty_snap())
step("Exactly one brick died even though the ball grazed the row below")
assert_false(app.bricks[0].alive)
assert_true(app.bricks[8].alive)
assert_equal(alive_bricks(app), 31)
assert_equal(app.score, 10)
assert_equal(app.ball_vy, 220.0)
```

</details>

#### losing a non-final life resets ball and paddle and keeps playing

- losing a non-final life resets ball and paddle and keeps playing
- Move the paddle off-center, then let the ball fall out
- Ball and paddle are back at their serve positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("losing a non-final life resets ball and paddle and keeps playing")
var app = started_game()
step("Move the paddle off-center, then let the ball fall out")
step_logic_n(app, held_snap(RIGHT_KEY), 10)
app.ball_y = 650.0
app.ball_vy = 220.0
step_logic_once(app, empty_snap())
assert_equal(app.state, GameState.Playing)
assert_equal(app.lives, 2)
step("Ball and paddle are back at their serve positions")
assert_equal(app.ball_x, 400.0)
assert_equal(app.ball_y, 551.0)
assert_equal(app.ball_vx, 140.0)
assert_equal(app.ball_vy, -220.0)
assert_equal(app.paddle_x, 350.0)
```

</details>

#### clearing the last brick wins the game

- clearing the last brick wins the game
- Leave only the first brick alive, ball rising into it


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clearing the last brick wins the game")
var app = started_game()
step("Leave only the first brick alive, ball rising into it")
kill_all_but_first(app)
assert_equal(alive_bricks(app), 1)
val target = app.bricks[0]
app.ball_x = target.x + target.w / 2.0
app.ball_y = target.y + target.h + 6.0
app.ball_vx = 0.0
app.ball_vy = -220.0
step_logic_once(app, empty_snap())
assert_equal(alive_bricks(app), 0)
assert_equal(app.state, GameState.GameOver)
assert_true(app.won)
assert_equal(app.score, 10)
```

</details>

#### independently produced scripted sessions hash identically

- independently produced scripted sessions hash identically
- Run the same 400-step scripted session twice from scratch
- An inverted input script produces a different hash


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("independently produced scripted sessions hash identically")
step("Run the same 400-step scripted session twice from scratch")
val a = run_scripted_session(false)
val b = run_scripted_session(false)
assert_equal(a, b)
step("An inverted input script produces a different hash")
val c = run_scripted_session(true)
assert_not_equal(a, c)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G3.2/G3.3)`
- **Design:** `src/app/game.breakout/game.spl, src/lib/nogc_sync_mut/game2d/input/{snapshot,api}.spl`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `82a07f7679dbc9a92eb2dec0bdd6fcd3bf5fbd7c45e97e06beb6f822c9bd43f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `82a07f7679dbc9a92eb2dec0bdd6fcd3bf5fbd7c45e97e06beb6f822c9bd43f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `82a07f7679dbc9a92eb2dec0bdd6fcd3bf5fbd7c45e97e06beb6f822c9bd43f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/game2d/breakout_event_animation_spec.spl
mirror: doc/06_spec/03_system/game2d/breakout_event_animation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/game2d/breakout_event_animation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/game2d/breakout_event_animation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/game2d/breakout_event_animation_spec.spl:168:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'held space without a press edge never starts the game' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/game2d/breakout_event_animation_spec.spl:182:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enter press edge starts the game like space' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/game2d/breakout_event_animation_spec.spl:192:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'game over restarts only on a fresh press edge and fully resets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
