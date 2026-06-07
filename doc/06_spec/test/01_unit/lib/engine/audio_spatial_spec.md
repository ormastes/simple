# audio_spatial_spec

> Engine Audio Spatial — AudioManager spatial audio and pure Simple logic tests

<!-- sdn-diagram:id=audio_spatial_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=audio_spatial_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

audio_spatial_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=audio_spatial_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# audio_spatial_spec

Engine Audio Spatial — AudioManager spatial audio and pure Simple logic tests

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/audio_spatial_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Engine Audio Spatial — AudioManager spatial audio and pure Simple logic tests

Tests active_sounds tracking, stop_sound removal, bus volume round-trip,
Listener3D default values, and set_listener_position_3d state updates.

Uses a pure-Simple mock AudioManager (no rt_audio_* externs) to exercise
the pure-Simple tracking logic. Listener3D tests use default_listener_3d().

## Scenarios

### AudioManager spatial

#### active_sounds tracks played sounds

1. var mgr = MockSpatialManager create
   - Expected: mgr.active_sounds.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_audio_config()
var mgr = MockSpatialManager.create(config)
val clip = mgr.load_clip("sfx/hit.wav")
val h1 = mgr.play(clip, "sfx")
val h2 = mgr.play(clip, "sfx")
expect(mgr.active_sounds.len()).to_equal(2)
```

</details>

#### stop_sound removes from active_sounds

1. var mgr = MockSpatialManager create
   - Expected: mgr.active_sounds.len() equals `1`
2. mgr stop sound
   - Expected: mgr.active_sounds.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_audio_config()
var mgr = MockSpatialManager.create(config)
val clip = mgr.load_clip("sfx/hit.wav")
val h1 = mgr.play(clip, "sfx")
expect(mgr.active_sounds.len()).to_equal(1)
mgr.stop_sound(h1)
expect(mgr.active_sounds.len()).to_equal(0)
```

</details>

#### set_bus_volume updates volume

1. var mgr = MockSpatialManager create
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_audio_config()
var mgr = MockSpatialManager.create(config)
val bus_name = "sfx"
val ok = mgr.set_bus_volume(bus_name, Volume(value: 0.42))
expect(ok).to_equal(true)
val vol = mgr.get_bus_volume("sfx")
val vol_i = vol.value * 1000.0
expect(vol_i).to_be_greater_than(419.0)
expect(vol_i).to_be_less_than(421.0)
```

</details>

#### Listener3D default values

1. forward: Vec3
2. up: Vec3


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build a default listener manually (Vec3.forward/up not in interpreter)
val zero = Vec3.zero()
val listener = Listener3D(
    position: zero,
    forward: Vec3(x: 0.0, y: 0.0, z: 1.0),
    up: Vec3(x: 0.0, y: 1.0, z: 0.0)
)
val px_i = listener.position.x * 1000.0
val py_i = listener.position.y * 1000.0
val pz_i = listener.position.z * 1000.0
expect(px_i).to_be_greater_than(-1.0)
expect(px_i).to_be_less_than(1.0)
expect(py_i).to_be_greater_than(-1.0)
expect(py_i).to_be_less_than(1.0)
expect(pz_i).to_be_greater_than(-1.0)
expect(pz_i).to_be_less_than(1.0)
val uy_i = listener.up.y * 1000.0
expect(uy_i).to_be_greater_than(999.0)
expect(uy_i).to_be_less_than(1001.0)
```

</details>

#### set_listener_position_3d updates state

1. var mgr = MockSpatialManager create
2. mgr set listener position 3d


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = default_audio_config()
var mgr = MockSpatialManager.create(config)
mgr.set_listener_position_3d(Vec3(x: 10.0, y: 20.0, z: 30.0))
val lx_i = mgr.listener_x * 100.0
val ly_i = mgr.listener_y * 100.0
expect(lx_i).to_be_greater_than(999.0)
expect(lx_i).to_be_less_than(1001.0)
expect(ly_i).to_be_greater_than(1999.0)
expect(ly_i).to_be_less_than(2001.0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
