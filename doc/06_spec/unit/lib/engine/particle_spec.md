# particle_spec

> Particle System — ParticleEmitter2D Tests

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
| Source | `test/unit/lib/engine/particle_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Particle System — ParticleEmitter2D Tests

Tests particle spawning, lifetime removal, and render command emission.

## Scenarios

### ParticleEmitter2D

#### starts with zero particles

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts with zero particles
   - Expected: emitter.particle_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with zero particles")
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

- spawns particles when emitting


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("spawns particles when emitting")
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

- removes dead particles after their lifetime
   - Expected: emitter.particle_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes dead particles after their lifetime")
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

- emits render commands for live particles
   - Expected: buf.len() equals `count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits render commands for live particles")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1caf98869d4be05cdf9a2f7ef7eed3c62e996f2214f16f996a30aa3054a3cf57`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1caf98869d4be05cdf9a2f7ef7eed3c62e996f2214f16f996a30aa3054a3cf57`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1caf98869d4be05cdf9a2f7ef7eed3c62e996f2214f16f996a30aa3054a3cf57`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/engine/particle_spec.spl
mirror: doc/06_spec/unit/lib/engine/particle_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/engine/particle_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/engine/particle_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/engine/particle_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/engine/particle_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts with zero particles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/engine/particle_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'spawns particles when emitting' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/engine/particle_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'removes dead particles after their lifetime' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
