# audio_spec

> Engine Audio — AudioManager silent backend tests

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# audio_spec

Engine Audio — AudioManager silent backend tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/audio_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Audio — AudioManager silent backend tests

Tests AudioManager creation, clip loading/caching, sound handle generation,
bus volume control, master volume, and mute/unmute.

Uses a pure-Simple mock AudioManager (no rt_audio_* externs) to exercise the
pure-Simple logic: bus tracking, volume round-trips, handle generation, caching.

## Scenarios

### AudioManager

#### create initializes with 3 default buses

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- create initializes with 3 default buses


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("create initializes with 3 default buses")
val config = default_audio_config()
val mgr = MockAudioManager.create(config)
val sfx_vol = mgr.get_bus_volume("sfx")
val music_vol = mgr.get_bus_volume("music")
val ui_vol = mgr.get_bus_volume("ui")
val sfx_i = sfx_vol.value * 1000.0
val music_i = music_vol.value * 1000.0
val ui_i = ui_vol.value * 1000.0
expect(sfx_i).to_be_greater_than(999.0)
expect(sfx_i).to_be_less_than(1001.0)
expect(music_i).to_be_greater_than(999.0)
expect(music_i).to_be_less_than(1001.0)
expect(ui_i).to_be_greater_than(999.0)
expect(ui_i).to_be_less_than(1001.0)
```

</details>

#### load_clip returns valid clip

- load_clip returns valid clip
   - Expected: clip.path equals `sfx/hit.wav`
   - Expected: clip.is_loaded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("load_clip returns valid clip")
val config = default_audio_config()
var mgr = MockAudioManager.create(config)
val clip = mgr.load_clip("sfx/hit.wav")
expect(clip.path).to_equal("sfx/hit.wav")
expect(clip.is_loaded).to_equal(true)
```

</details>

#### load_clip_cached returns same on second call

- load_clip_cached returns same on second call
   - Expected: clip1.path equals `clip2.path`
   - Expected: clip1.is_loaded equals `clip2.is_loaded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("load_clip_cached returns same on second call")
val config = default_audio_config()
var mgr = MockAudioManager.create(config)
val clip1 = mgr.load_clip_cached("sfx/hit.wav")
val clip2 = mgr.load_clip_cached("sfx/hit.wav")
expect(clip1.path).to_equal(clip2.path)
expect(clip1.is_loaded).to_equal(clip2.is_loaded)
```

</details>

#### play returns valid SoundHandle

- play returns valid SoundHandle
   - Expected: handle.is_valid() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("play returns valid SoundHandle")
val config = default_audio_config()
var mgr = MockAudioManager.create(config)
val clip = mgr.load_clip("sfx/hit.wav")
val handle = mgr.play(clip, "sfx")
expect(handle.is_valid()).to_equal(true)
expect(handle.playback_handle).to_be_greater_than(0)
```

</details>

#### each play gives unique handle

- each play gives unique handle
   - Expected: different_1_2 is true
   - Expected: different_2_3 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("each play gives unique handle")
val config = default_audio_config()
var mgr = MockAudioManager.create(config)
val clip = mgr.load_clip("sfx/hit.wav")
val h1 = mgr.play(clip, "sfx")
val h2 = mgr.play(clip, "sfx")
val h3 = mgr.play(clip, "sfx")
val different_1_2 = h1.playback_handle != h2.playback_handle
val different_2_3 = h2.playback_handle != h3.playback_handle
expect(different_1_2).to_equal(true)
expect(different_2_3).to_equal(true)
```

</details>

#### set_bus_volume and get_bus_volume round-trip

- set_bus_volume and get_bus_volume round-trip
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_bus_volume and get_bus_volume round-trip")
val config = default_audio_config()
var mgr = MockAudioManager.create(config)
val from_name = "sfx"
val ok = mgr.set_bus_volume(from_name, Volume(value: 0.5))
expect(ok).to_equal(true)
val vol = mgr.get_bus_volume("sfx")
val vol_i = vol.value * 1000.0
expect(vol_i).to_be_greater_than(499.0)
expect(vol_i).to_be_less_than(501.0)
```

</details>

#### set_master_volume and get_master_volume round-trip

- set_master_volume and get_master_volume round-trip


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_master_volume and get_master_volume round-trip")
val config = default_audio_config()
var mgr = MockAudioManager.create(config)
mgr.set_master_volume(Volume(value: 0.75))
val vol = mgr.get_master_volume()
val vol_i = vol.value * 1000.0
expect(vol_i).to_be_greater_than(749.0)
expect(vol_i).to_be_less_than(751.0)
```

</details>

#### mute_bus and unmute_bus

- mute_bus and unmute_bus
   - Expected: muted is true
   - Expected: unmuted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mute_bus and unmute_bus")
val config = default_audio_config()
var mgr = MockAudioManager.create(config)
val from_name = "music"
val muted = mgr.mute_bus(from_name)
expect(muted).to_equal(true)
val unmuted = mgr.unmute_bus(from_name)
expect(unmuted).to_equal(true)
```

</details>

#### set_bus_volume returns false for unknown bus

- set_bus_volume returns false for unknown bus
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_bus_volume returns false for unknown bus")
val config = default_audio_config()
var mgr = MockAudioManager.create(config)
val from_name = "nonexistent"
val ok = mgr.set_bus_volume(from_name, Volume(value: 0.5))
expect(ok).to_equal(false)
```

</details>

#### get_bus_volume returns 0 for unknown bus

- get_bus_volume returns 0 for unknown bus


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_bus_volume returns 0 for unknown bus")
val config = default_audio_config()
val mgr = MockAudioManager.create(config)
val vol = mgr.get_bus_volume("nonexistent")
val vol_i = vol.value * 1000.0
expect(vol_i).to_be_greater_than(-1.0)
expect(vol_i).to_be_less_than(1.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `8b02bdabefbdd54721ff7c7bb6aa07dc5bc133412cf704ba441ec6ca59ec000d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b02bdabefbdd54721ff7c7bb6aa07dc5bc133412cf704ba441ec6ca59ec000d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b02bdabefbdd54721ff7c7bb6aa07dc5bc133412cf704ba441ec6ca59ec000d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/engine/audio_spec.spl
mirror: doc/06_spec/01_unit/lib/engine/audio_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/engine/audio_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/engine/audio_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/engine/audio_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'create initializes with 3 default buses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/engine/audio_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'load_clip returns valid clip' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/engine/audio_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'load_clip_cached returns same on second call' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
