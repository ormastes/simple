# Vehicle Specification

> <details>

<!-- sdn-diagram:id=vehicle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=vehicle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

vehicle_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=vehicle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vehicle Specification

## Scenarios

### VehicleConfig

#### creates default config

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VehicleConfig.default_config()
expect(cfg.mass).to_equal(1500.0)
expect(cfg.max_steer_angle).to_equal(35.0)
expect(cfg.engine_force).to_equal(5000.0)
```

</details>

### Vehicle

#### creates at position

1. var car = Vehicle new
   - Expected: car.position_x equals `10.0`
   - Expected: car.position_y equals `20.0`
   - Expected: car.get_speed() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VehicleConfig.default_config()
var car = Vehicle.new(10.0, 20.0, cfg)
expect(car.position_x).to_equal(10.0)
expect(car.position_y).to_equal(20.0)
expect(car.get_speed()).to_equal(0.0)
```

</details>

#### adds wheels

1. var car = Vehicle new
   - Expected: car.wheel_count() equals `1`
   - Expected: idx equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VehicleConfig.default_config()
var car = Vehicle.new(0.0, 0.0, cfg)
val w = Wheel.new(-0.8, 1.2, 0.3, true, true)
val idx = car.add_wheel(w)
expect(car.wheel_count()).to_equal(1)
expect(idx).to_equal(0)
```

</details>

#### accelerates with throttle

1. var car = Vehicle new
2. car set throttle
3. car update


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VehicleConfig.default_config()
var car = Vehicle.new(0.0, 0.0, cfg)
car.set_throttle(1.0)
car.update(0.1)
expect(car.get_speed()).to_be_greater_than(0.0)
expect(car.position_x).to_be_greater_than(0.0)
```

</details>

#### brakes to stop

1. var car = Vehicle new
2. car set throttle
3. car update
4. car set throttle
5. car set brake
6. car update


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VehicleConfig.default_config()
var car = Vehicle.new(0.0, 0.0, cfg)
car.set_throttle(1.0)
car.update(0.1)
val speed_before = car.get_speed()
expect(speed_before).to_be_greater_than(0.0)
car.set_throttle(0.0)
car.set_brake(1.0)
car.update(1.0)
expect(car.get_speed()).to_be_less_than(speed_before)
```

</details>

#### stops immediately with stop()

1. var car = Vehicle new
2. car set throttle
3. car update
4. car stop
   - Expected: car.get_speed() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VehicleConfig.default_config()
var car = Vehicle.new(0.0, 0.0, cfg)
car.set_throttle(1.0)
car.update(0.1)
car.stop()
expect(car.get_speed()).to_equal(0.0)
```

</details>

#### retrieves wheel by index

1. var car = Vehicle new
2. car add wheel
   - Expected: wh.radius equals `0.35`
   - Expected: wh.steering is true
   - Expected: wh.drive is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VehicleConfig.default_config()
var car = Vehicle.new(0.0, 0.0, cfg)
val w = Wheel.new(-0.8, 1.2, 0.35, true, false)
car.add_wheel(w)
if val Some(wh) = car.get_wheel(0):
    expect(wh.radius).to_equal(0.35)
    expect(wh.steering).to_equal(true)
    expect(wh.drive).to_equal(false)
```

</details>

#### stationary without throttle

1. var car = Vehicle new
2. car update
   - Expected: car.position_x equals `5.0`
   - Expected: car.position_y equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = VehicleConfig.default_config()
var car = Vehicle.new(5.0, 10.0, cfg)
car.update(1.0)
expect(car.position_x).to_equal(5.0)
expect(car.position_y).to_equal(10.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/vehicle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- VehicleConfig
- Vehicle

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
