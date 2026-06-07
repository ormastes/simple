# audio_spec

> Engine Audio — AudioManager silent backend tests

<!-- sdn-diagram:id=audio_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=audio_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

audio_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=audio_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Audio — AudioManager silent backend tests

Tests AudioManager creation, clip loading/caching, sound handle generation,
bus volume control, master volume, and mute/unmute.

Uses a pure-Simple mock AudioManager (no rt_audio_* externs) to exercise the
pure-Simple logic: bus tracking, volume round-trips, handle generation, caching.

## Scenarios

### AudioManager

#### create initializes with 3 default buses

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = MockAudioManager create
   - Expected: clip.path equals `sfx/hit.wav`
   - Expected: clip.is_loaded is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_audio_config()
var mgr = MockAudioManager.create(config)
val clip = mgr.load_clip("sfx/hit.wav")
expect(clip.path).to_equal("sfx/hit.wav")
expect(clip.is_loaded).to_equal(true)
```

</details>

#### load_clip_cached returns same on second call

1. var mgr = MockAudioManager create
   - Expected: clip1.path equals `clip2.path`
   - Expected: clip1.is_loaded equals `clip2.is_loaded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_audio_config()
var mgr = MockAudioManager.create(config)
val clip1 = mgr.load_clip_cached("sfx/hit.wav")
val clip2 = mgr.load_clip_cached("sfx/hit.wav")
expect(clip1.path).to_equal(clip2.path)
expect(clip1.is_loaded).to_equal(clip2.is_loaded)
```

</details>

#### play returns valid SoundHandle

1. var mgr = MockAudioManager create
   - Expected: handle.is_valid() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_audio_config()
var mgr = MockAudioManager.create(config)
val clip = mgr.load_clip("sfx/hit.wav")
val handle = mgr.play(clip, "sfx")
expect(handle.is_valid()).to_equal(true)
expect(handle.playback_handle).to_be_greater_than(0)
```

</details>

#### each play gives unique handle

1. var mgr = MockAudioManager create
   - Expected: different_1_2 is true
   - Expected: different_2_3 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = MockAudioManager create
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = MockAudioManager create
2. mgr set master volume


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = MockAudioManager create
   - Expected: muted is true
   - Expected: unmuted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. var mgr = MockAudioManager create
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_audio_config()
var mgr = MockAudioManager.create(config)
val from_name = "nonexistent"
val ok = mgr.set_bus_volume(from_name, Volume(value: 0.5))
expect(ok).to_equal(false)
```

</details>

#### get_bus_volume returns 0 for unknown bus

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
