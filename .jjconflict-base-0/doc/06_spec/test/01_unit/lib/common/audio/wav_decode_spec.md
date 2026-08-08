# Wav Decode Specification

> <details>

<!-- sdn-diagram:id=wav_decode_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wav_decode_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wav_decode_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wav_decode_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wav Decode Specification

## Scenarios

### wav_decode decode_wav

#### hand-built minimal PCM16 WAV (not produced by the encoder)

#### decodes one 0x4000 PCM16 sample to exactly 0.5

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = decode_wav(KAT_PCM16_8KHZ_ONE_SAMPLE)
var got: [f32] = []
if val Ok(a) = r:
    got = a.samples
expect(got).to_equal([0.5])
```

</details>

#### reports sample_rate=8000 from the fmt chunk

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = decode_wav(KAT_PCM16_8KHZ_ONE_SAMPLE)
var sr: i64 = -1
if val Ok(a) = r:
    sr = a.sample_rate
expect(sr).to_equal(8000)
```

</details>

#### reports channels=1 from the fmt chunk

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = decode_wav(KAT_PCM16_8KHZ_ONE_SAMPLE)
var ch: i64 = -1
if val Ok(a) = r:
    ch = a.channels
expect(ch).to_equal(1)
```

</details>

#### unknown chunk between fmt and data is skipped by size, not misread

#### still decodes the sample after a spliced-in 4-byte unknown chunk

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Same fmt/data as KAT_PCM16_8KHZ_ONE_SAMPLE, with a "JUNK" chunk
# (declared size 4, 4 zero bytes) inserted between fmt and data.
# RIFF size = 4(WAVE) + (8+16 fmt) + (8+4 JUNK) + (8+2 data) = 50.
val bytes: [u8] = [
    82u8, 73u8, 70u8, 70u8, 50u8, 0u8, 0u8, 0u8,
    87u8, 65u8, 86u8, 69u8,
    102u8, 109u8, 116u8, 32u8, 16u8, 0u8, 0u8, 0u8,
    1u8, 0u8, 1u8, 0u8, 64u8, 31u8, 0u8, 0u8, 64u8, 31u8, 0u8, 0u8, 2u8, 0u8, 16u8, 0u8,
    74u8, 85u8, 78u8, 75u8, 4u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
    100u8, 97u8, 116u8, 97u8, 2u8, 0u8, 0u8, 0u8,
    0u8, 64u8
]
val r = decode_wav(bytes)
var got: [f32] = []
if val Ok(a) = r:
    got = a.samples
expect(got).to_equal([0.5])
```

</details>

#### malformed input

#### rejects bytes missing the RIFF tag with a clear Err

- has marker = e contains
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bad: [u8] = [88u8, 88u8, 88u8, 88u8, 0u8, 0u8, 0u8, 0u8, 87u8, 65u8, 86u8, 69u8]
val r = decode_wav(bad)
var has_marker = false
if val Err(e) = r:
    has_marker = e.contains("RIFF")
expect(has_marker).to_equal(true)
```

</details>

#### rejects an unsupported audio_format/bits combination (8-bit PCM) with a clear Err

- has marker = e contains
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Same shape as KAT_PCM16_8KHZ_ONE_SAMPLE but bits_per_sample=8
# and a 2-byte data chunk (2 samples of 1 byte each).
val bytes: [u8] = [
    82u8, 73u8, 70u8, 70u8, 38u8, 0u8, 0u8, 0u8,
    87u8, 65u8, 86u8, 69u8,
    102u8, 109u8, 116u8, 32u8, 16u8, 0u8, 0u8, 0u8,
    1u8, 0u8, 1u8, 0u8, 64u8, 31u8, 0u8, 0u8, 64u8, 31u8, 0u8, 0u8, 1u8, 0u8, 8u8, 0u8,
    100u8, 97u8, 116u8, 97u8, 2u8, 0u8, 0u8, 0u8,
    128u8, 128u8
]
val r = decode_wav(bytes)
var has_marker = false
if val Err(e) = r:
    has_marker = e.contains("unsupported format")
expect(has_marker).to_equal(true)
```

</details>

### wav_decode / wav_encode round-trip

#### PCM16 — exact except at the documented +-1.0 clamp

#### round-trips [0.0, 0.5, -0.5, 1.0] to [0.0, 0.5, -0.5, 32767/32768]

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val samples: [f32] = [0.0, 0.5, -0.5, 1.0]
val bytes = encode_wav_pcm16(samples, 1, 44100)
val r = decode_wav(bytes)
var got: [f32] = []
if val Ok(a) = r:
    got = a.samples
expect(got).to_equal([0.0, 0.5, -0.5, 0.999969482421875])
```

</details>

#### float32 — bit-exact

#### round-trips [0.0, 0.5, -0.5, 1.0] exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val samples: [f32] = [0.0, 0.5, -0.5, 1.0]
val bytes = encode_wav_f32(samples, 1, 44100)
val r = decode_wav(bytes)
var got: [f32] = []
if val Ok(a) = r:
    got = a.samples
expect(got).to_equal([0.0, 0.5, -0.5, 1.0])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/audio/wav_decode_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- wav_decode decode_wav
- wav_decode / wav_encode round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
