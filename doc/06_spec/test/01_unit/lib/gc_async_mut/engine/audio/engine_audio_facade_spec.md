# Engine Audio Facade Specification

> <details>

<!-- sdn-diagram:id=engine_audio_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine_audio_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine_audio_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine_audio_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine Audio Facade Specification

## Scenarios

### gc_async_mut engine audio facade

#### re-exports audio types and defaults

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cfg = default_audio_config()
expect(cfg.master_volume.value).to_equal(1.0)
val listener = default_listener_3d()
expect(listener.up.y).to_equal(1.0)
val handle = SoundHandle(playback_handle: 7, clip_path: "hit.wav", bus_name: "sfx", is_spatial: false)
expect(handle.is_valid()).to_equal(true)
```

</details>

#### re-exports pure audio helpers

1. var chain = EffectsChain empty
2. chain add
   - Expected: chain.count() equals `1`
   - Expected: AudioGroup.root("master").is_root() is true
3. var snap = MixerSnapshot new
4. snap set volume
   - Expected: snap.group_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Source | `test/01_unit/lib/gc_async_mut/engine/audio/engine_audio_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
