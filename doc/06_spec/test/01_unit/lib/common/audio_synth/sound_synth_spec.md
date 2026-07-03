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
| 15 | 15 | 0 | 0 |

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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
