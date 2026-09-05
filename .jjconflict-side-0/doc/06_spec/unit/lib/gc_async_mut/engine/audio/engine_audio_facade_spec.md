# Engine Audio Facade Specification

> Tests covering gc_async_mut engine audio facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Audio Facade Specification

## Scenarios

### gc_async_mut engine audio facade

#### re-exports audio types and defaults

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports audio types and defaults
   - Expected: cfg.master_volume.value equals `1.0`
   - Expected: listener.up.y equals `1.0`
   - Expected: handle.is_valid() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports audio types and defaults")
val cfg = default_audio_config()
expect(cfg.master_volume.value).to_equal(1.0)
val listener = default_listener_3d()
expect(listener.up.y).to_equal(1.0)
val handle = SoundHandle(playback_handle: 7, clip_path: "hit.wav", bus_name: "sfx", is_spatial: false)
expect(handle.is_valid()).to_equal(true)
```

</details>

#### re-exports pure audio helpers

- re-exports pure audio helpers
   - Expected: pitch equals `1.0`
   - Expected: chain.count() equals `1`
   - Expected: AudioGroup.root("master").is_root() is true
   - Expected: snap.group_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports pure audio helpers")
val pitch = compute_doppler_pitch(Vec3.zero(), Vec3.zero(), Vec3.forward(), Vec3.zero(), default_doppler_config())
expect(pitch).to_equal(1.0)
var chain = EffectsChain.empty()
chain.add(AudioEffect.LowPass(effect: LowPassEffect(cutoff_hz: 800.0)))
expect(chain.count()).to_equal(1)
expect(AudioGroup.root("master").is_root()).to_equal(true)
var snap = MixerSnapshot.new("combat")
snap.set_volume("music", 0.3)
expect(snap.group_count()).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/gc_async_mut/engine/audio/engine_audio_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut engine audio facade.
- gc_async_mut engine audio facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `281b8fb8db3b4dcc0136d669a327ec2cbd0ee2cbda78af7d830957da01cad1cd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `281b8fb8db3b4dcc0136d669a327ec2cbd0ee2cbda78af7d830957da01cad1cd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `281b8fb8db3b4dcc0136d669a327ec2cbd0ee2cbda78af7d830957da01cad1cd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/gc_async_mut/engine/audio/engine_audio_facade_spec.spl
mirror: doc/06_spec/unit/lib/gc_async_mut/engine/audio/engine_audio_facade_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/gc_async_mut/engine/audio/engine_audio_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/gc_async_mut/engine/audio/engine_audio_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/gc_async_mut/engine/audio/engine_audio_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/gc_async_mut/engine/audio/engine_audio_facade_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports audio types and defaults' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/gc_async_mut/engine/audio/engine_audio_facade_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports pure audio helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
