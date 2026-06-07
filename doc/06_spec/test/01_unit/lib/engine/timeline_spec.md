# Timeline Specification

> 1. var track = TimelineTrack new

<!-- sdn-diagram:id=timeline_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=timeline_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

timeline_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=timeline_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Timeline Specification

## Scenarios

### TimelineTrack

#### creates empty track

1. var track = TimelineTrack new
   - Expected: track.key_count() equals `0`
   - Expected: track.duration() equals `0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var track = TimelineTrack.new("position", "x")
expect(track.key_count()).to_equal(0)
expect(track.duration()).to_equal(0.0)
```

</details>

#### adds keys and computes duration

1. var track = TimelineTrack new
2. track add key
3. track add key
4. track add key
   - Expected: track.key_count() equals `3`
   - Expected: track.duration() equals `2.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var track = TimelineTrack.new("move", "x")
track.add_key(0.0, 0.0, "linear")
track.add_key(1.0, 10.0, "linear")
track.add_key(2.0, 5.0, "linear")
expect(track.key_count()).to_equal(3)
expect(track.duration()).to_equal(2.0)
```

</details>

#### samples linear interpolation

1. var track = TimelineTrack new
2. track add key
3. track add key
   - Expected: mid equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var track = TimelineTrack.new("move", "x")
track.add_key(0.0, 0.0, "linear")
track.add_key(1.0, 10.0, "linear")
val mid = track.sample(0.5)
expect(mid).to_equal(5.0)
```

</details>

#### samples before first key returns first value

1. var track = TimelineTrack new
2. track add key
3. track add key
   - Expected: track.sample(0.0) equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var track = TimelineTrack.new("t", "x")
track.add_key(1.0, 5.0, "linear")
track.add_key(2.0, 10.0, "linear")
expect(track.sample(0.0)).to_equal(5.0)
```

</details>

#### samples after last key returns last value

1. var track = TimelineTrack new
2. track add key
3. track add key
   - Expected: track.sample(5.0) equals `10.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var track = TimelineTrack.new("t", "x")
track.add_key(0.0, 0.0, "linear")
track.add_key(1.0, 10.0, "linear")
expect(track.sample(5.0)).to_equal(10.0)
```

</details>

#### samples with ease_in easing

1. var track = TimelineTrack new
2. track add key
3. track add key
   - Expected: mid equals `25.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var track = TimelineTrack.new("t", "x")
track.add_key(0.0, 0.0, "ease_in")
track.add_key(1.0, 100.0, "ease_in")
val mid = track.sample(0.5)
# ease_in: t*t, so at 0.5 -> 0.25 * 100 = 25
expect(mid).to_equal(25.0)
```

</details>

### Timeline

#### creates timeline with duration

1. var tl = Timeline new
   - Expected: tl.track_count() equals `0`
   - Expected: tl.is_playing() is false
   - Expected: tl.duration equals `5.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tl = Timeline.new("cutscene", 5.0)
expect(tl.track_count()).to_equal(0)
expect(tl.is_playing()).to_equal(false)
expect(tl.duration).to_equal(5.0)
```

</details>

#### plays and updates time

1. var tl = Timeline new
2. tl play
   - Expected: tl.is_playing() is true
3. tl update
   - Expected: tl.get_current_time() equals `0.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tl = Timeline.new("test", 2.0)
tl.play()
expect(tl.is_playing()).to_equal(true)
tl.update(0.5)
expect(tl.get_current_time()).to_equal(0.5)
```

</details>

<details>
<summary>Advanced: stops at duration when not looping</summary>

#### stops at duration when not looping

1. var tl = Timeline new
2. tl play
3. tl update
   - Expected: tl.get_current_time() equals `1.0`
   - Expected: tl.is_playing() is false
   - Expected: tl.is_finished() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tl = Timeline.new("test", 1.0)
tl.play()
tl.update(2.0)
expect(tl.get_current_time()).to_equal(1.0)
expect(tl.is_playing()).to_equal(false)
expect(tl.is_finished()).to_equal(true)
```

</details>


</details>

#### seeks to specific time

1. var tl = Timeline new
2. tl seek
   - Expected: tl.get_current_time() equals `3.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tl = Timeline.new("test", 5.0)
tl.seek(3.0)
expect(tl.get_current_time()).to_equal(3.0)
```

</details>

#### stop resets time

1. var tl = Timeline new
2. tl play
3. tl update
4. tl stop
   - Expected: tl.get_current_time() equals `0.0`
   - Expected: tl.is_playing() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tl = Timeline.new("test", 5.0)
tl.play()
tl.update(2.0)
tl.stop()
expect(tl.get_current_time()).to_equal(0.0)
expect(tl.is_playing()).to_equal(false)
```

</details>

#### pause keeps current time

1. var tl = Timeline new
2. tl play
3. tl update
4. tl pause
   - Expected: tl.get_current_time() equals `2.0`
   - Expected: tl.is_playing() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tl = Timeline.new("test", 5.0)
tl.play()
tl.update(2.0)
tl.pause()
expect(tl.get_current_time()).to_equal(2.0)
expect(tl.is_playing()).to_equal(false)
```

</details>

#### samples track at given time

1. var tl = Timeline new
2. var track = TimelineTrack new
3. track add key
4. track add key
5. tl add track
   - Expected: val_at_1 equals `50.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var tl = Timeline.new("test", 2.0)
var track = TimelineTrack.new("pos", "x")
track.add_key(0.0, 0.0, "linear")
track.add_key(2.0, 100.0, "linear")
tl.add_track(track)
val val_at_1 = tl.sample_track(0, 1.0)
expect(val_at_1).to_equal(50.0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/engine/timeline_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TimelineTrack
- Timeline

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
