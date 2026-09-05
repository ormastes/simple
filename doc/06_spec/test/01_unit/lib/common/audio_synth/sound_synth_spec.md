# Sound Synth Specification

> <details>

<!-- sdn-diagram:id=sound_synth_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sound_synth_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sound_synth_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sound_synth_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sound Synth Specification

## Scenarios

### sound_synth gen_sine

#### 1kHz tone at 8kHz sample rate, 1ms duration

#### returns a buffer of exactly duration_ms * sample_rate / 1000 frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = gen_sine(1000.0, 1.0, 8000)
expect(s.len()).to_equal(8)
```

</details>

#### sample[0] is exactly 0.0 (sin at t=0)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = gen_sine(1000.0, 1.0, 8000)
expect(s[0]).to_equal(0.0)
```

</details>

#### sample[2] is exactly 1.0 (peak at the quarter period)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = gen_sine(1000.0, 1.0, 8000)
expect(s[2]).to_equal(1.0)
```

</details>

#### sample[1] matches sin(pi/4) to double precision

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = gen_sine(1000.0, 1.0, 8000)
expect(s[1]).to_equal(0.7071067811865475)
```

</details>

#### sample[6] is exactly -1.0 (trough at three-quarter period)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = gen_sine(1000.0, 1.0, 8000)
expect(s[6]).to_equal(-1.0)
```

</details>

### sound_synth gen_square

#### 1kHz tone at 8kHz sample rate — sign of the equivalent sine

#### is +1.0 for the first half period and -1.0 for the second

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sq = gen_square(1000.0, 1.0, 8000)
expect(sq[0]).to_equal(1.0)
expect(sq[1]).to_equal(1.0)
expect(sq[2]).to_equal(1.0)
expect(sq[3]).to_equal(1.0)
expect(sq[5]).to_equal(-1.0)
expect(sq[6]).to_equal(-1.0)
expect(sq[7]).to_equal(-1.0)
```

</details>

### sound_synth gen_white_noise

#### determinism

#### two calls with the same seed produce identical buffers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n1 = gen_white_noise(2.0, 8000, 42)
val n2 = gen_white_noise(2.0, 8000, 42)
expect(n1).to_equal(n2)
```

</details>

#### produces different buffers for different seeds

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n1 = gen_white_noise(2.0, 8000, 42)
val n2 = gen_white_noise(2.0, 8000, 7)
val differs = n1 != n2
expect(differs).to_equal(true)
```

</details>

### sound_synth apply_adsr

#### attack=2ms, decay=2ms, sustain=0.5, release=2ms, 10 frames @ 1000Hz

#### zeroes the first sample when attack_ms > 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ones: [f64] = [1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0]
val env = apply_adsr(ones, 2.0, 2.0, 0.5, 2.0, 1000)
expect(env[0]).to_equal(0.0)
```

</details>

#### reaches sustain_level exactly at attack_frames + decay_frames (index 4)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ones: [f64] = [1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0]
val env = apply_adsr(ones, 2.0, 2.0, 0.5, 2.0, 1000)
expect(env[4]).to_equal(0.5)
```

</details>

#### holds sustain_level flat through the sustain region

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ones: [f64] = [1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0]
val env = apply_adsr(ones, 2.0, 2.0, 0.5, 2.0, 1000)
expect(env[5]).to_equal(0.5)
expect(env[6]).to_equal(0.5)
expect(env[7]).to_equal(0.5)
```

</details>

#### decays to exactly 0.0 by the last sample (end of release_ms)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ones: [f64] = [1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0, 1.0]
val env = apply_adsr(ones, 2.0, 2.0, 0.5, 2.0, 1000)
expect(env[9]).to_equal(0.0)
```

</details>

### sound_synth mix

#### layered voices

#### sums buffers sample-accurately at a known offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mixed = mix([[0.25, 0.125], [0.25, 0.125], [0.25, 0.125]])
expect(mixed[0]).to_equal(0.75)
expect(mixed[1]).to_equal(0.375)
```

</details>

#### clamps the sum to 1.0 when voices overdrive

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mixed = mix([[0.5, 0.5], [0.5, 0.5], [0.5, 0.5]])
expect(mixed[0]).to_equal(1.0)
expect(mixed[1]).to_equal(1.0)
```

</details>

#### treats a shorter buffer's missing tail samples as 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mixed = mix([[1.0], [0.25, 0.25]])
expect(mixed.len()).to_equal(2)
expect(mixed[0]).to_equal(1.0)
expect(mixed[1]).to_equal(0.25)
```

</details>

### sound_synth reverb

#### impulse response, sample_rate=8000, room_size=0.5

#### wet=0 returns the input unchanged, bit-exact (pure dry pass-through)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val imp = _impulse(1000)
val out = reverb(imp, 8000, 0.5, 0.0)
expect(out).to_equal(imp)
```

</details>

#### wet=1 is exactly 0.0 for every frame before the first comb echo (smallest comb delay = 237 frames at 8000Hz)

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val imp = _impulse(1000)
val out = reverb(imp, 8000, 0.5, 1.0)
var all_zero = true
var i: i64 = 0
while i < 237:
    if out[i] != 0.0:
        all_zero = false
    i = i + 1
expect(all_zero).to_equal(true)
```

</details>

#### wet=1 first echo lands exactly at frame 237 with amplitude 0.7*0.7*0.5 (comb feedback through 2 series allpasses)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val imp = _impulse(1000)
val out = reverb(imp, 8000, 0.5, 1.0)
expect(out[237]).to_equal(0.7 * 0.7 * 0.5)
```

</details>

#### energy decay — 100ms 440Hz tone burst padded to 2000 frames @8000Hz, room_size=0.5, wet=0.5

#### sums |sample| over the second half strictly less than the first half

- buf push
- var j: i64 = tone len
- buf push
   - Expected: decays is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tone = gen_sine(440.0, 100.0, 8000)
var buf: [f64] = []
for s in tone:
    buf.push(s)
var j: i64 = tone.len()
while j < 2000:
    buf.push(0.0)
    j = j + 1
val rv = reverb(buf, 8000, 0.5, 0.5)
var first_sum: f64 = 0.0
var second_sum: f64 = 0.0
var k: i64 = 0
while k < 1000:
    var v = rv[k]
    if v < 0.0:
        v = -v
    first_sum = first_sum + v
    k = k + 1
while k < 2000:
    var v = rv[k]
    if v < 0.0:
        v = -v
    second_sum = second_sum + v
    k = k + 1
val decays = second_sum < first_sum
expect(decays).to_equal(true)
```

</details>

#### determinism

#### two calls with identical parameters produce byte-identical buffers

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val imp = _impulse(1000)
val a = reverb(imp, 8000, 0.5, 0.5)
val b = reverb(imp, 8000, 0.5, 0.5)
expect(a).to_equal(b)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/audio_synth/sound_synth_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- sound_synth gen_sine
- sound_synth gen_square
- sound_synth gen_white_noise
- sound_synth apply_adsr
- sound_synth mix
- sound_synth reverb

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
