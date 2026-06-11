# Audio Specification

> 1. sound play

<!-- sdn-diagram:id=audio_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=audio_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

audio_spec
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
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Audio Specification

## Scenarios

### AudioSystem

#### plays sounds

1. sound play
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sound = AudioSource.new("test_sound")
sound.play()
check(sound.is_playing() == true)
```

</details>

#### plays music

1. music play
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val music = AudioSource.new("background_music")
music.play()
check(music.is_playing() == true)
```

</details>

#### controls volume

1. set master volume
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
set_master_volume(0.5)
check(get_master_volume() == 0.5)
```

</details>

#### pauses and resumes

1. sound play
2. sound pause
3. check
4. sound resume
5. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sound = AudioSource.new("test_sound")
sound.play()
sound.pause()
check(sound.is_playing() == false)
sound.resume()
check(sound.is_playing() == true)
```

</details>

#### handles 3D positioning

1. sound set position
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
