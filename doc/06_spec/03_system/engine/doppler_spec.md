# Doppler Specification

> Tests covering Doppler — stationary, Doppler — source moving toward listener, Doppler — source moving away from listener, Doppler — disabled.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Doppler Specification

## Scenarios

### Doppler — stationary

#### stationary listener and source gives pitch 1.0

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- stationary listener and source gives pitch 1.0
   - Expected: pitch > 0.99 is true
   - Expected: pitch < 1.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stationary listener and source gives pitch 1.0")
val config = default_doppler_config()
val zero = Vec3(x: 0.0, y: 0.0, z: 0.0)
val pos = Vec3(x: 10.0, y: 0.0, z: 0.0)
val pitch = compute_doppler_pitch(zero, zero, pos, zero, config)
expect(pitch > 0.99).to_equal(true)
expect(pitch < 1.01).to_equal(true)
```

</details>

### Doppler — source moving toward listener

#### pitch is greater than 1.0

- pitch is greater than 1.0
   - Expected: pitch > 1.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pitch is greater than 1.0")
val config = default_doppler_config()
val l_pos = Vec3(x: 0.0, y: 0.0, z: 0.0)
val l_vel = Vec3(x: 0.0, y: 0.0, z: 0.0)
val s_pos = Vec3(x: 100.0, y: 0.0, z: 0.0)
val s_vel = Vec3(x: -50.0, y: 0.0, z: 0.0)
val pitch = compute_doppler_pitch(l_pos, l_vel, s_pos, s_vel, config)
expect(pitch > 1.0).to_equal(true)
```

</details>

### Doppler — source moving away from listener

#### pitch is less than 1.0

- pitch is less than 1.0
   - Expected: pitch < 1.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pitch is less than 1.0")
val config = default_doppler_config()
val l_pos = Vec3(x: 0.0, y: 0.0, z: 0.0)
val l_vel = Vec3(x: 0.0, y: 0.0, z: 0.0)
val s_pos = Vec3(x: 100.0, y: 0.0, z: 0.0)
val s_vel = Vec3(x: 50.0, y: 0.0, z: 0.0)
val pitch = compute_doppler_pitch(l_pos, l_vel, s_pos, s_vel, config)
expect(pitch < 1.0).to_equal(true)
```

</details>

### Doppler — disabled

#### disabled doppler returns 1.0 regardless of velocities

- disabled doppler returns 1.0 regardless of velocities
   - Expected: pitch > 0.99 is true
   - Expected: pitch < 1.01 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("disabled doppler returns 1.0 regardless of velocities")
val config = DopplerConfig(enabled: false, speed_of_sound: 343.0, factor: 1.0)
val l_pos = Vec3(x: 0.0, y: 0.0, z: 0.0)
val l_vel = Vec3(x: 0.0, y: 0.0, z: 0.0)
val s_pos = Vec3(x: 100.0, y: 0.0, z: 0.0)
val s_vel = Vec3(x: -50.0, y: 0.0, z: 0.0)
val pitch = compute_doppler_pitch(l_pos, l_vel, s_pos, s_vel, config)
expect(pitch > 0.99).to_equal(true)
expect(pitch < 1.01).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/engine/doppler_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Doppler — stationary, Doppler — source moving toward listener, Doppler — source moving away from listener, Doppler — disabled.
- Doppler — stationary
- Doppler — source moving toward listener
- Doppler — source moving away from listener
- Doppler — disabled

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b8168e9e27d2a47b7315ed24526a9ac4da9af94c9a3789b6f762855f5326b9c1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b8168e9e27d2a47b7315ed24526a9ac4da9af94c9a3789b6f762855f5326b9c1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b8168e9e27d2a47b7315ed24526a9ac4da9af94c9a3789b6f762855f5326b9c1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/engine/doppler_spec.spl
mirror: doc/06_spec/03_system/engine/doppler_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/engine/doppler_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/engine/doppler_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/engine/doppler_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stationary listener and source gives pitch 1.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/doppler_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pitch is greater than 1.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/engine/doppler_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pitch is less than 1.0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
