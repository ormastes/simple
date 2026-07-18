# Sound Asset Sdn Specification

> <details>

<!-- sdn-diagram:id=sound_asset_sdn_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sound_asset_sdn_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sound_asset_sdn_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sound_asset_sdn_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sound Asset Sdn Specification

## Scenarios

### sound_asset_sdn load_sound_asset

#### minimal tone sound.sdn

#### parses freq_hz=440, duration_ms=200 from source.tone

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_write_fixtures()).to_equal(true)
val r = load_sound_asset(TONE_PATH)
if val Ok(a) = r:
    expect(a.kind).to_equal("sfx")
    expect(a.sample_rate).to_equal(8000)
    expect(a.source.kind).to_equal("tone")
    expect(a.source.wave).to_equal("sine")
    expect(a.source.freq_hz).to_equal(440.0)
    expect(a.source.duration_ms).to_equal(200.0)
if val Err(e) = r:
    expect(e).to_equal("")
```

</details>

#### missing required source.type

#### rejects with a path-qualified error

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_write_fixtures()).to_equal(true)
val r = load_sound_asset(MISSING_SOURCE_PATH)
if val Ok(_a) = r:
    expect("loaded").to_equal("should have been rejected")
if val Err(e) = r:
    val has_marker = e.contains("source.type")
    expect(has_marker).to_equal(true)
```

</details>

#### sequence kind with 2 events

#### parses events at exact at_ms offsets

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_write_fixtures()).to_equal(true)
val r = load_sound_asset(SEQUENCE_PATH)
if val Ok(a) = r:
    expect(a.kind).to_equal("sequence")
    expect(a.events.len()).to_equal(2)
    expect(a.events[0].at_ms).to_equal(0)
    expect(a.events[0].clip).to_equal("kick.wav")
    expect(a.events[1].at_ms).to_equal(250)
    expect(a.events[1].clip).to_equal("snare.wav")
if val Err(e) = r:
    expect(e).to_equal("")
```

</details>

#### missing top-level sound block

#### rejects with a clear error instead of a default asset

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_write_fixtures()).to_equal(true)
val r = load_sound_asset(NOT_SOUND_PATH)
if val Ok(_a) = r:
    expect("loaded").to_equal("should have been rejected")
if val Err(e) = r:
    val has_marker = e.contains("sound")
    expect(has_marker).to_equal(true)
```

</details>

#### missing file

#### rejects with a not-found error

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = load_sound_asset("build/test-artifacts/sound_asset_sdn_spec_does_not_exist.sdn")
if val Ok(_a) = r:
    expect("loaded").to_equal("should have been rejected")
if val Err(e) = r:
    val has_marker = e.contains("not found")
    expect(has_marker).to_equal(true)
```

</details>

#### reverb effect

<details>
<summary>Advanced: parses room_size=0.5 and wet=0.3 from effects[0]</summary>

#### parses room_size=0.5 and wet=0.3 from effects[0]

- ok =
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_write_fixtures()).to_equal(true)
val r = load_sound_asset(REVERB_PATH)
var ok = false
if val Ok(a) = r:
    ok = (a.effects.len() == 1 and a.effects[0].kind == "reverb" and
        a.effects[0].room_size == 0.5 and a.effects[0].wet == 0.3)
expect(ok).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: rejects room_size out of [0,1] with a path-qualified error</summary>

#### rejects room_size out of [0,1] with a path-qualified error

- has marker = e contains
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_write_fixtures()).to_equal(true)
val r = load_sound_asset(REVERB_BAD_ROOM_PATH)
var has_marker = false
if val Err(e) = r:
    has_marker = e.contains("effects[0].room_size")
expect(has_marker).to_equal(true)
```

</details>


</details>

#### rejects wet out of [0,1] with a path-qualified error

- has marker = e contains
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_write_fixtures()).to_equal(true)
val r = load_sound_asset(REVERB_BAD_WET_PATH)
var has_marker = false
if val Err(e) = r:
    has_marker = e.contains("effects[0].wet")
expect(has_marker).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/game2d/audio/sound_asset_sdn_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- sound_asset_sdn load_sound_asset

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
