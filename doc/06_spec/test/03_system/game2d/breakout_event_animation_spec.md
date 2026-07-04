# Breakout Event Handling & Animation Oracles

> Closes the event-handling and animation gaps left open by `breakout_production_spec.spl` (long-session smoke) and `game2d_event_replay_spec.spl` (frame-hash replay):

<!-- sdn-diagram:id=breakout_event_animation_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=breakout_event_animation_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

breakout_event_animation_spec -> std
breakout_event_animation_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=breakout_event_animation_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

- var app = Game new game
- Feed five frames of SPACE held down but not press-edged
- step logic n
- assert equal
- A real press edge then starts the game exactly once
- step logic once
- assert equal
- Continuing the hold after the edge does not re-trigger a reset
- step logic n
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var app = Game new game
- Press ENTER on the menu
- step logic once
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var app = Game.new_game()
step("Press ENTER on the menu")
step_logic_once(app, press_snap(ENTER_KEY))
assert_equal(app.state, GameState.Playing)
assert_equal(app.score, 0)
assert_equal(app.lives, 3)
```

</details>

#### game over restarts only on a fresh press edge and fully resets

- var app = started game
- Force the last life to be lost
- step logic once
- assert equal
- assert false
- assert equal
- SPACE held over from before the game ended does not restart
- step logic n
- assert equal
- A fresh press edge restarts with score, lives, bricks and ball reset
- step logic once
- assert equal
- assert equal
- assert equal
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var app = started game
- park ball
- assert equal
- Hold LEFT for 20 fixed steps
- step logic n
- Hold RIGHT for 40 fixed steps
- step logic n


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var app = started game
- park ball
- Run 60 fixed steps with no input at all
- step logic n
- assert equal
- Run 60 fixed steps with LEFT and RIGHT held together
- step logic n
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var app = started game
- park ball
- Hold LEFT far longer than needed to reach the wall
- step logic n
- assert equal
- Hold RIGHT far longer than needed to reach the other wall
- step logic n
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var app = started game
- The start-press frame itself does not advance physics
- assert equal
- assert equal
- After 10 collision-free steps the ball is at the analytic position
- step logic n
- After 30 total steps it is still exactly on the line
- step logic n


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var app = started game
- Stage the ball just off the left wall moving left
- step logic once
- assert equal
- assert equal
- Stage the ball just off the right wall moving right
- step logic once
- assert equal
- assert equal
- Stage the ball just below the top wall moving up
- step logic once
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var app = started game
- Drop the ball straight onto the paddle center
- step logic once
- assert equal
- assert equal
- assert equal
- Drop the ball halfway between center and right paddle edge
- step logic once
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var app = started game
- Stage the ball rising into the first brick of the top row
- assert true
- step logic once
- Exactly one brick died even though the ball grazed the row below
- assert false
- assert true
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var app = started game
- Move the paddle off-center, then let the ball fall out
- step logic n
- step logic once
- assert equal
- assert equal
- Ball and paddle are back at their serve positions
- assert equal
- assert equal
- assert equal
- assert equal
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- var app = started game
- Leave only the first brick alive, ball rising into it
- kill all but first
- assert equal
- step logic once
- assert equal
- assert equal
- assert true
- assert equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Run the same 400-step scripted session twice from scratch
- assert equal
- An inverted input script produces a different hash
- assert not equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Requirements:** [doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G3.2/G3.3)](doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (G3.2/G3.3))
- **Design:** [src/app/game.breakout/game.spl, src/lib/nogc_sync_mut/game2d/input/{snapshot,api}.spl](src/app/game.breakout/game.spl, src/lib/nogc_sync_mut/game2d/input/{snapshot,api}.spl)


</details>
