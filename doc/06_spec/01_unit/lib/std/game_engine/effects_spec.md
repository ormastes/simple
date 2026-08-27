# Effects Specification

> Tests covering GameEffect, EffectContext.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Effects Specification

## Scenarios

### GameEffect

#### creates RenderEffect

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates RenderEffect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates RenderEffect")
val effect = GameEffect.RenderEffect("draw_sprite")
expect effect is GameEffect.RenderEffect(_)
```

</details>

#### creates PhysicsEffect

- creates PhysicsEffect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates PhysicsEffect")
val effect = GameEffect.PhysicsEffect("apply_force")
expect effect is GameEffect.PhysicsEffect(_)
```

</details>

#### creates AudioEffect

- creates AudioEffect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates AudioEffect")
val effect = GameEffect.AudioEffect("play_sound")
expect effect is GameEffect.AudioEffect(_)
```

</details>

#### creates IOEffect

- creates IOEffect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates IOEffect")
val effect = GameEffect.IOEffect("load_asset")
expect effect is GameEffect.IOEffect(_)
```

</details>

#### creates EngineSyncEffect

- creates EngineSyncEffect


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates EngineSyncEffect")
val effect = GameEffect.EngineSyncEffect("update_scene")
expect effect is GameEffect.EngineSyncEffect(_)
```

</details>

### EffectContext

#### creation

#### creates empty context

- creates empty context


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates empty context")
val ctx = EffectContext.new()
expect ctx.is_empty()
expect ctx.effect_count() == 0
```

</details>

#### starts as async safe

- starts as async safe


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts as async safe")
val ctx = EffectContext.new()
expect ctx.is_async_safe()
```

</details>

#### effect management

#### adds effects

- adds effects


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds effects")
var ctx = EffectContext.new()
ctx.add_effect(GameEffect.RenderEffect("draw"))
expect ctx.has_effects()
expect ctx.effect_count() == 1
```

</details>

#### checks for specific effect

- checks for specific effect


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks for specific effect")
var ctx = EffectContext.new()
ctx.add_effect(GameEffect.PhysicsEffect("collision"))
expect ctx.has_effect("collision")
expect not ctx.has_effect("other")
```

</details>

#### async safety

#### remains async safe with render effects

- remains async safe with render effects


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remains async safe with render effects")
var ctx = EffectContext.new()
ctx.add_effect(GameEffect.RenderEffect("draw"))
expect ctx.is_async_safe()
```

</details>

#### becomes unsafe with sync effects

- becomes unsafe with sync effects


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("becomes unsafe with sync effects")
var ctx = EffectContext.new()
ctx.add_effect(GameEffect.EngineSyncEffect("main_thread_op"))
expect not ctx.is_async_safe()
```

</details>

#### summary

#### provides context summary

- provides context summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides context summary")
var ctx = EffectContext.new()
ctx.add_effect(GameEffect.RenderEffect("draw"))
val summary = ctx.summary()
expect "1 effects" in summary or "1 effect" in summary
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/std/game_engine/effects_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering GameEffect, EffectContext.
- GameEffect
- EffectContext

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `1af3f82e36282fd056dc0c21564700f45594269dd229cd6fc6c4ea4ceea42d95`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1af3f82e36282fd056dc0c21564700f45594269dd229cd6fc6c4ea4ceea42d95`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1af3f82e36282fd056dc0c21564700f45594269dd229cd6fc6c4ea4ceea42d95`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/std/game_engine/effects_spec.spl
mirror: doc/06_spec/01_unit/lib/std/game_engine/effects_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/std/game_engine/effects_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/std/game_engine/effects_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/std/game_engine/effects_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates RenderEffect' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/game_engine/effects_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates PhysicsEffect' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/std/game_engine/effects_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates AudioEffect' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
