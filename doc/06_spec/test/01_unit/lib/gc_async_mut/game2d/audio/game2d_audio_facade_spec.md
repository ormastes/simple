# Game2d Audio Facade Specification

> <details>

<!-- sdn-diagram:id=game2d_audio_facade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=game2d_audio_facade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

game2d_audio_facade_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=game2d_audio_facade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Game2d Audio Facade Specification

## Scenarios

### gc_async_mut game2d audio facade

#### re-exports sound metadata and audio diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sfx = Sound.sfx("click.wav")
expect(sfx.bus_name).to_equal("sfx")
expect(sfx.looped).to_equal(false)
expect(sfx.spatial).to_equal(false)
expect(sfx.with_volume(0.5).volume).to_equal(0.5)
expect(Sound.music("theme.ogg").looped).to_equal(true)
expect(Sound.spatial_sfx("hit.wav").spatial).to_equal(true)
expect(Sound(clip_path: "", bus_name: "sfx", volume: 1.0, looped: false, spatial: false).is_null()).to_equal(true)

expect(AudioError.backend_missing().code).to_equal("GAME-AUDIO-001")
expect(play(sfx).is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/game2d/audio/game2d_audio_facade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- gc_async_mut game2d audio facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
