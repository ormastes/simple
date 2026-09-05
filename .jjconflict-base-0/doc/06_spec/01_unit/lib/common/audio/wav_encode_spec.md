# Wav Encode Specification

> Tests covering wav_encode encode_wav_pcm16, wav_encode encode_wav_f32.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wav Encode Specification

## Scenarios

### wav_encode encode_wav_pcm16

#### RIFF/WAVE/fmt header — mono, 44100 Hz

#### emits exact RIFF/WAVE/fmt/data chunk tags and sizes

- emits exact RIFF/WAVE/fmt/data chunk tags and sizes
   - Expected: bytes.len() equals `52)  # 44-byte header + 4 samples * 2 bytes`
   - Expected: bytes[0] equals `82u8`
   - Expected: bytes[1] equals `73u8`
   - Expected: bytes[2] equals `70u8`
   - Expected: bytes[3] equals `70u8`
   - Expected: bytes[4] equals `44u8`
   - Expected: bytes[5] equals `0u8`
   - Expected: bytes[6] equals `0u8`
   - Expected: bytes[7] equals `0u8`
   - Expected: bytes[8] equals `87u8`
   - Expected: bytes[9] equals `65u8`
   - Expected: bytes[10] equals `86u8`
   - Expected: bytes[11] equals `69u8`
   - Expected: bytes[12] equals `102u8`
   - Expected: bytes[13] equals `109u8`
   - Expected: bytes[14] equals `116u8`
   - Expected: bytes[15] equals `32u8`
   - Expected: bytes[16] equals `16u8`
   - Expected: bytes[17] equals `0u8`
   - Expected: bytes[18] equals `0u8`
   - Expected: bytes[19] equals `0u8`
   - Expected: bytes[20] equals `1u8`
   - Expected: bytes[21] equals `0u8`
   - Expected: bytes[22] equals `1u8`
   - Expected: bytes[23] equals `0u8`
   - Expected: bytes[24] equals `68u8`
   - Expected: bytes[25] equals `172u8`
   - Expected: bytes[26] equals `0u8`
   - Expected: bytes[27] equals `0u8`
   - Expected: bytes[28] equals `136u8`
   - Expected: bytes[29] equals `88u8`
   - Expected: bytes[30] equals `1u8`
   - Expected: bytes[31] equals `0u8`
   - Expected: bytes[32] equals `2u8`
   - Expected: bytes[33] equals `0u8`
   - Expected: bytes[34] equals `16u8`
   - Expected: bytes[35] equals `0u8`
   - Expected: bytes[36] equals `100u8`
   - Expected: bytes[37] equals `97u8`
   - Expected: bytes[38] equals `116u8`
   - Expected: bytes[39] equals `97u8`
   - Expected: bytes[40] equals `8u8`
   - Expected: bytes[41] equals `0u8`
   - Expected: bytes[42] equals `0u8`
   - Expected: bytes[43] equals `0u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 61 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits exact RIFF/WAVE/fmt/data chunk tags and sizes")
val bytes = encode_wav_pcm16(SAMPLES, 1, 44100)
expect(bytes.len()).to_equal(52)  # 44-byte header + 4 samples * 2 bytes
# "RIFF"
expect(bytes[0]).to_equal(82u8)
expect(bytes[1]).to_equal(73u8)
expect(bytes[2]).to_equal(70u8)
expect(bytes[3]).to_equal(70u8)
# RIFF chunk size = 36 + data_len(8) = 44, little-endian
expect(bytes[4]).to_equal(44u8)
expect(bytes[5]).to_equal(0u8)
expect(bytes[6]).to_equal(0u8)
expect(bytes[7]).to_equal(0u8)
# "WAVE"
expect(bytes[8]).to_equal(87u8)
expect(bytes[9]).to_equal(65u8)
expect(bytes[10]).to_equal(86u8)
expect(bytes[11]).to_equal(69u8)
# "fmt "
expect(bytes[12]).to_equal(102u8)
expect(bytes[13]).to_equal(109u8)
expect(bytes[14]).to_equal(116u8)
expect(bytes[15]).to_equal(32u8)
# fmt chunk size = 16
expect(bytes[16]).to_equal(16u8)
expect(bytes[17]).to_equal(0u8)
expect(bytes[18]).to_equal(0u8)
expect(bytes[19]).to_equal(0u8)
# audio_format = 1 (PCM)
expect(bytes[20]).to_equal(1u8)
expect(bytes[21]).to_equal(0u8)
# channels = 1
expect(bytes[22]).to_equal(1u8)
expect(bytes[23]).to_equal(0u8)
# sample_rate = 44100 LE = 0x0000AC44
expect(bytes[24]).to_equal(68u8)
expect(bytes[25]).to_equal(172u8)
expect(bytes[26]).to_equal(0u8)
expect(bytes[27]).to_equal(0u8)
# byte_rate = sample_rate * block_align = 88200 LE = 0x00015888
expect(bytes[28]).to_equal(136u8)
expect(bytes[29]).to_equal(88u8)
expect(bytes[30]).to_equal(1u8)
expect(bytes[31]).to_equal(0u8)
# block_align = channels * bytes_per_sample = 2
expect(bytes[32]).to_equal(2u8)
expect(bytes[33]).to_equal(0u8)
# bits per sample = 16
expect(bytes[34]).to_equal(16u8)
expect(bytes[35]).to_equal(0u8)
# "data"
expect(bytes[36]).to_equal(100u8)
expect(bytes[37]).to_equal(97u8)
expect(bytes[38]).to_equal(116u8)
expect(bytes[39]).to_equal(97u8)
# data chunk size = 4 samples * 2 bytes = 8
expect(bytes[40]).to_equal(8u8)
expect(bytes[41]).to_equal(0u8)
expect(bytes[42]).to_equal(0u8)
expect(bytes[43]).to_equal(0u8)
```

</details>

#### exact PCM16 sample bytes at documented rounding (trunc(s*32768), clamped)

#### 0.0 -> 0x0000, 0.5 -> 0x4000, -0.5 -> 0xC000 (u16), 1.0 -> clamped 0x7FFF

- 0.0 -> 0x0000, 0.5 -> 0x4000, -0.5 -> 0xC000 (u16), 1.0 -> clamped 0x7FFF
   - Expected: bytes[44] equals `0u8`
   - Expected: bytes[45] equals `0u8`
   - Expected: bytes[46] equals `0u8`
   - Expected: bytes[47] equals `64u8`
   - Expected: bytes[48] equals `0u8`
   - Expected: bytes[49] equals `192u8`
   - Expected: bytes[50] equals `255u8`
   - Expected: bytes[51] equals `127u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("0.0 -> 0x0000, 0.5 -> 0x4000, -0.5 -> 0xC000 (u16), 1.0 -> clamped 0x7FFF")
val bytes = encode_wav_pcm16(SAMPLES, 1, 44100)
# sample 0: 0.0 -> 0
expect(bytes[44]).to_equal(0u8)
expect(bytes[45]).to_equal(0u8)
# sample 1: 0.5 -> trunc(0.5 * 32768) = 16384 = 0x4000
expect(bytes[46]).to_equal(0u8)
expect(bytes[47]).to_equal(64u8)
# sample 2: -0.5 -> trunc(-0.5 * 32768) = -16384 -> u16 0xC000
expect(bytes[48]).to_equal(0u8)
expect(bytes[49]).to_equal(192u8)
# sample 3: 1.0 -> trunc(1.0 * 32768) = 32768, clamped to 32767 = 0x7FFF
expect(bytes[50]).to_equal(255u8)
expect(bytes[51]).to_equal(127u8)
```

</details>

#### stereo channel field

#### sets channels=2 and block_align=4 for a stereo buffer

- sets channels=2 and block_align=4 for a stereo buffer
   - Expected: bytes[22] equals `2u8`
   - Expected: bytes[23] equals `0u8`
   - Expected: bytes[32] equals `4u8`
   - Expected: bytes[33] equals `0u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets channels=2 and block_align=4 for a stereo buffer")
val stereo: [f32] = [0.0, 0.0, 1.0, -1.0]
val bytes = encode_wav_pcm16(stereo, 2, 8000)
expect(bytes[22]).to_equal(2u8)
expect(bytes[23]).to_equal(0u8)
expect(bytes[32]).to_equal(4u8)
expect(bytes[33]).to_equal(0u8)
```

</details>

#### determinism

#### produces byte-identical output across two separate encode calls

- produces byte-identical output across two separate encode calls
   - Expected: bytes1 equals `bytes2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces byte-identical output across two separate encode calls")
val bytes1 = encode_wav_pcm16(SAMPLES, 1, 44100)
val bytes2 = encode_wav_pcm16(SAMPLES, 1, 44100)
expect(bytes1).to_equal(bytes2)
```

</details>

### wav_encode encode_wav_f32

#### bit-exact IEEE-754 float32 samples, format code 3

#### sets audio_format=3 and emits exact little-endian IEEE-754 bit patterns

- sets audio_format=3 and emits exact little-endian IEEE-754 bit patterns
   - Expected: bytes.len() equals `60)  # 44-byte header + 4 samples * 4 bytes`
   - Expected: bytes[20] equals `3u8`
   - Expected: bytes[21] equals `0u8`
   - Expected: bytes[44] equals `0u8`
   - Expected: bytes[45] equals `0u8`
   - Expected: bytes[46] equals `0u8`
   - Expected: bytes[47] equals `0u8`
   - Expected: bytes[48] equals `0u8`
   - Expected: bytes[49] equals `0u8`
   - Expected: bytes[50] equals `0u8`
   - Expected: bytes[51] equals `63u8`
   - Expected: bytes[52] equals `0u8`
   - Expected: bytes[53] equals `0u8`
   - Expected: bytes[54] equals `0u8`
   - Expected: bytes[55] equals `191u8`
   - Expected: bytes[56] equals `0u8`
   - Expected: bytes[57] equals `0u8`
   - Expected: bytes[58] equals `128u8`
   - Expected: bytes[59] equals `63u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sets audio_format=3 and emits exact little-endian IEEE-754 bit patterns")
val bytes = encode_wav_f32(SAMPLES, 1, 44100)
expect(bytes.len()).to_equal(60)  # 44-byte header + 4 samples * 4 bytes
# audio_format = 3 (IEEE float)
expect(bytes[20]).to_equal(3u8)
expect(bytes[21]).to_equal(0u8)
# sample 0: 0.0 -> 0x00000000
expect(bytes[44]).to_equal(0u8)
expect(bytes[45]).to_equal(0u8)
expect(bytes[46]).to_equal(0u8)
expect(bytes[47]).to_equal(0u8)
# sample 1: 0.5 -> 0x3F000000 LE
expect(bytes[48]).to_equal(0u8)
expect(bytes[49]).to_equal(0u8)
expect(bytes[50]).to_equal(0u8)
expect(bytes[51]).to_equal(63u8)
# sample 2: -0.5 -> 0xBF000000 LE
expect(bytes[52]).to_equal(0u8)
expect(bytes[53]).to_equal(0u8)
expect(bytes[54]).to_equal(0u8)
expect(bytes[55]).to_equal(191u8)
# sample 3: 1.0 -> 0x3F800000 LE
expect(bytes[56]).to_equal(0u8)
expect(bytes[57]).to_equal(0u8)
expect(bytes[58]).to_equal(128u8)
expect(bytes[59]).to_equal(63u8)
```

</details>

#### determinism

#### produces byte-identical output across two separate encode calls

- produces byte-identical output across two separate encode calls
   - Expected: bytes1 equals `bytes2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("produces byte-identical output across two separate encode calls")
val bytes1 = encode_wav_f32(SAMPLES, 1, 44100)
val bytes2 = encode_wav_f32(SAMPLES, 1, 44100)
expect(bytes1).to_equal(bytes2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/audio/wav_encode_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering wav_encode encode_wav_pcm16, wav_encode encode_wav_f32.
- wav_encode encode_wav_pcm16
- wav_encode encode_wav_f32

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c3e7d8241e63648639e6db5a0314db1d28d82ddee1df46b4ad324c277cdb3af6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c3e7d8241e63648639e6db5a0314db1d28d82ddee1df46b4ad324c277cdb3af6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c3e7d8241e63648639e6db5a0314db1d28d82ddee1df46b4ad324c277cdb3af6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/audio/wav_encode_spec.spl
mirror: doc/06_spec/01_unit/lib/common/audio/wav_encode_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/audio/wav_encode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/audio/wav_encode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/audio/wav_encode_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits exact RIFF/WAVE/fmt/data chunk tags and sizes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/audio/wav_encode_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario '0.0 -> 0x0000, 0.5 -> 0x4000, -0.5 -> 0xC000 (u16), 1.0 -> clamped 0x7FFF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/audio/wav_encode_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sets channels=2 and block_align=4 for a stereo buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
