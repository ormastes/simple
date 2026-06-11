# particle_spec

> Particle System — ParticleEmitter2D Tests

<!-- sdn-diagram:id=particle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=particle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

particle_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=particle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# particle_spec

Particle System — ParticleEmitter2D Tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/particle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Particle System — ParticleEmitter2D Tests

Tests particle spawning, lifetime removal, and render command emission.

## Scenarios

### ParticleEmitter2D

#### starts with zero particles

1. start color: EngineColor white
2. end color: EngineColor transparent
3. direction: Vec2
4. gravity: Vec2 zero
5. var emitter = ParticleEmitter2D create
   - Expected: emitter.particle_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = ParticleConfig(
    emission_rate: 10.0,
    min_lifetime: 0.5,
    max_lifetime: 1.0,
    min_speed: 10.0,
    max_speed: 50.0,
    min_size: 2.0,
    max_size: 4.0,
    start_color: EngineColor.white(),
    end_color: EngineColor.transparent(),
    direction: Vec2(x: 0.0, y: -1.0),
    spread_angle: 0.3,
    gravity: Vec2.zero()
)
var emitter = ParticleEmitter2D.create(config, Vec2(x: 100.0, y: 100.0), ZIndex(value: 5))
expect(emitter.particle_count()).to_equal(0)
```

</details>

#### spawns particles when emitting

1. start color: EngineColor red
2. end color: EngineColor transparent
3. direction: Vec2
4. gravity: Vec2 zero
5. var emitter = ParticleEmitter2D create
6. emitter start
7. emitter update


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = ParticleConfig(
    emission_rate: 100.0,
    min_lifetime: 1.0,
    max_lifetime: 2.0,
    min_speed: 10.0,
    max_speed: 50.0,
    min_size: 2.0,
    max_size: 4.0,
    start_color: EngineColor.red(),
    end_color: EngineColor.transparent(),
    direction: Vec2(x: 0.0, y: -1.0),
    spread_angle: 0.5,
    gravity: Vec2.zero()
)
var emitter = ParticleEmitter2D.create(config, Vec2(x: 200.0, y: 200.0), ZIndex(value: 5))
emitter.start()
emitter.update(Seconds(value: 0.1))
# 100 particles/sec * 0.1 sec = 10 particles
expect(emitter.particle_count()).to_be_greater_than(0)
```

</details>

#### removes dead particles after their lifetime

1. start color: EngineColor green
2. end color: EngineColor transparent
3. direction: Vec2
4. gravity: Vec2 zero
5. var emitter = ParticleEmitter2D create
6. emitter start
7. emitter update
8. emitter stop
9. emitter update
   - Expected: emitter.particle_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = ParticleConfig(
    emission_rate: 50.0,
    min_lifetime: 0.1,
    max_lifetime: 0.1,
    min_speed: 10.0,
    max_speed: 10.0,
    min_size: 2.0,
    max_size: 2.0,
    start_color: EngineColor.green(),
    end_color: EngineColor.transparent(),
    direction: Vec2(x: 1.0, y: 0.0),
    spread_angle: 0.0,
    gravity: Vec2.zero()
)
var emitter = ParticleEmitter2D.create(config, Vec2.zero(), ZIndex(value: 0))
emitter.start()
emitter.update(Seconds(value: 0.05))
val count_after_spawn = emitter.particle_count()
expect(count_after_spawn).to_be_greater_than(0)
# Stop emitting, then advance past max lifetime
emitter.stop()
emitter.update(Seconds(value: 0.2))
expect(emitter.particle_count()).to_equal(0)
```

</details>

#### emits render commands for live particles

1. start color: EngineColor blue
2. end color: EngineColor transparent
3. direction: Vec2
4. gravity: Vec2
5. var emitter = ParticleEmitter2D create
6. emitter start
7. emitter update
8. var buf = RenderCommandBuffer create
9. emitter emit render commands
   - Expected: buf.len() equals `count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = ParticleConfig(
    emission_rate: 50.0,
    min_lifetime: 1.0,
    max_lifetime: 2.0,
    min_speed: 20.0,
    max_speed: 40.0,
    min_size: 3.0,
    max_size: 5.0,
    start_color: EngineColor.blue(),
    end_color: EngineColor.transparent(),
    direction: Vec2(x: 0.0, y: -1.0),
    spread_angle: 0.3,
    gravity: Vec2(x: 0.0, y: 50.0)
)
var emitter = ParticleEmitter2D.create(config, Vec2(x: 300.0, y: 300.0), ZIndex(value: 10))
emitter.start()
emitter.update(Seconds(value: 0.1))
val count = emitter.particle_count()
var buf = RenderCommandBuffer.create()
emitter.emit_render_commands(buf)
# One DrawRect per particle
expect(buf.len()).to_equal(count)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
