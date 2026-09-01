# Audio Specification

> Tests covering AudioSystem.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Audio Specification

## Scenarios

### AudioSystem

#### plays sounds

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- plays sounds


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("plays sounds")
val sound = AudioSource.new("test_sound")
sound.play()
check(sound.is_playing() == true)
```

</details>

#### plays music

- plays music


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("plays music")
val music = AudioSource.new("background_music")
music.play()
check(music.is_playing() == true)
```

</details>

#### controls volume

- controls volume


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("controls volume")
set_master_volume(0.5)
check(get_master_volume() == 0.5)
```

</details>

#### pauses and resumes

- pauses and resumes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pauses and resumes")
val sound = AudioSource.new("test_sound")
sound.play()
sound.pause()
check(sound.is_playing() == false)
sound.resume()
check(sound.is_playing() == true)
```

</details>

#### handles 3D positioning

- handles 3D positioning


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles 3D positioning")
val sound = AudioSource.new("positioned_sound")
sound.set_position(px=10.0, py=5.0, pz=-3.0)
check(sound.x == 10.0)
check(sound.y == 5.0)
check(sound.z == -3.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/game3d/audio_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering AudioSystem.
- AudioSystem

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `c25e340a60d54759e82c848e3eaa3fcaa0645ec0a02521e8711cfe99e4d4b15a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c25e340a60d54759e82c848e3eaa3fcaa0645ec0a02521e8711cfe99e4d4b15a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c25e340a60d54759e82c848e3eaa3fcaa0645ec0a02521e8711cfe99e4d4b15a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/game3d/audio_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/game3d/audio_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/game3d/audio_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/game3d/audio_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/game3d/audio_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'plays sounds' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/game3d/audio_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'plays music' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/game3d/audio_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'controls volume' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
