# character_controller_spec

> Engine Character Controller — CharacterController Tests

<!-- sdn-diagram:id=character_controller_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=character_controller_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

character_controller_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=character_controller_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# character_controller_spec

Engine Character Controller — CharacterController Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/character_controller_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Character Controller — CharacterController Tests

Tests character movement, gravity, jumping, ground detection, and slope handling.

## Scenarios

### CharacterConfig

#### creates default config

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = CharacterConfig.default_config()
expect(cfg.step_height).to_equal(0.3)
expect(cfg.slope_limit).to_equal(45.0)
expect(cfg.skin_width).to_equal(0.01)
expect(cfg.gravity).to_equal(9.81)
```

</details>

### CharacterController

#### initializes at given position

1. var ctrl = CharacterController new
   - Expected: ctrl.get_position_x() equals `5.0`
   - Expected: ctrl.get_position_y() equals `10.0`
   - Expected: ctrl.is_grounded() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = CharacterConfig.default_config()
var ctrl = CharacterController.new(5.0, 10.0, cfg)
expect(ctrl.get_position_x()).to_equal(5.0)
expect(ctrl.get_position_y()).to_equal(10.0)
expect(ctrl.is_grounded()).to_equal(false)
```

</details>

#### moves by displacement

1. var ctrl = CharacterController new
2. ctrl move by
   - Expected: ctrl.get_position_x() equals `3.0`
   - Expected: ctrl.get_position_y() equals `4.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = CharacterConfig.default_config()
var ctrl = CharacterController.new(0.0, 0.0, cfg)
ctrl.move_by(3.0, 4.0)
expect(ctrl.get_position_x()).to_equal(3.0)
expect(ctrl.get_position_y()).to_equal(4.0)
```

</details>

#### applies gravity when airborne

1. var ctrl = CharacterController new
2. ctrl apply gravity
   - Expected: ctrl.velocity_y equals `9.81`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = CharacterConfig.default_config()
var ctrl = CharacterController.new(0.0, 0.0, cfg)
ctrl.apply_gravity(1.0)
expect(ctrl.velocity_y).to_equal(9.81)
```

</details>

#### does not apply gravity when grounded

1. var ctrl = CharacterController new
2. ctrl set grounded
3. ctrl apply gravity
   - Expected: ctrl.velocity_y equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = CharacterConfig.default_config()
var ctrl = CharacterController.new(0.0, 0.0, cfg)
ctrl.set_grounded(true, 0.0, 0.0, 1.0)
ctrl.apply_gravity(1.0)
expect(ctrl.velocity_y).to_equal(0.0)
```

</details>

#### updates position from velocity

1. var ctrl = CharacterController new
2. ctrl set velocity
3. ctrl update
   - Expected: ctrl.get_position_x() equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = CharacterConfig.default_config()
var ctrl = CharacterController.new(0.0, 0.0, cfg)
ctrl.set_velocity(10.0, 0.0)
ctrl.update(0.5)
expect(ctrl.get_position_x()).to_equal(5.0)
```

</details>

#### sets grounded and zeros velocity_y

1. var ctrl = CharacterController new
2. ctrl set velocity
3. ctrl set grounded
   - Expected: ctrl.is_grounded() is true
   - Expected: ctrl.velocity_y equals `0.0`
   - Expected: ctrl.get_slope_angle() equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = CharacterConfig.default_config()
var ctrl = CharacterController.new(0.0, 0.0, cfg)
ctrl.set_velocity(0.0, 20.0)
ctrl.set_grounded(true, 10.0, 0.0, 1.0)
expect(ctrl.is_grounded()).to_equal(true)
expect(ctrl.velocity_y).to_equal(0.0)
expect(ctrl.get_slope_angle()).to_equal(10.0)
```

</details>

#### jumps when grounded

1. var ctrl = CharacterController new
2. ctrl set grounded
3. ctrl jump
   - Expected: ctrl.velocity_y equals `-5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = CharacterConfig.default_config()
var ctrl = CharacterController.new(0.0, 0.0, cfg)
ctrl.set_grounded(true, 0.0, 0.0, 1.0)
ctrl.jump(5.0)
expect(ctrl.velocity_y).to_equal(-5.0)
```

</details>

#### does not jump when airborne

1. var ctrl = CharacterController new
2. ctrl jump
   - Expected: ctrl.velocity_y equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = CharacterConfig.default_config()
var ctrl = CharacterController.new(0.0, 0.0, cfg)
ctrl.jump(5.0)
expect(ctrl.velocity_y).to_equal(0.0)
```

</details>

#### checks climbable slope

1. var ctrl = CharacterController new
2. ctrl set grounded
   - Expected: ctrl.can_climb_slope() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = CharacterConfig.default_config()
var ctrl = CharacterController.new(0.0, 0.0, cfg)
ctrl.set_grounded(true, 30.0, 0.0, 1.0)
expect(ctrl.can_climb_slope()).to_equal(true)
```

</details>

#### rejects steep slope

1. var ctrl = CharacterController new
2. ctrl set grounded
   - Expected: ctrl.can_climb_slope() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = CharacterConfig.default_config()
var ctrl = CharacterController.new(0.0, 0.0, cfg)
ctrl.set_grounded(true, 60.0, 0.0, 1.0)
expect(ctrl.can_climb_slope()).to_equal(false)
```

</details>

#### stops all velocity

1. var ctrl = CharacterController new
2. ctrl set velocity
3. ctrl stop
   - Expected: ctrl.velocity_x equals `0.0`
   - Expected: ctrl.velocity_y equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = CharacterConfig.default_config()
var ctrl = CharacterController.new(0.0, 0.0, cfg)
ctrl.set_velocity(5.0, 10.0)
ctrl.stop()
expect(ctrl.velocity_x).to_equal(0.0)
expect(ctrl.velocity_y).to_equal(0.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
