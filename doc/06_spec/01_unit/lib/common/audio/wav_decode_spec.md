# Wav Decode Specification

> Tests covering wav_decode decode_wav, wav_decode / wav_encode round-trip.

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

- decodes one 0x4000 PCM16 sample to exactly 0.5
   - Expected: got equals `[0.5]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes one 0x4000 PCM16 sample to exactly 0.5")
val r = decode_wav(KAT_PCM16_8KHZ_ONE_SAMPLE)
var got: [f32] = []
if val Ok(a) = r:
    got = a.samples
expect(got).to_equal([0.5])
```

</details>

#### reports sample_rate=8000 from the fmt chunk

- reports sample_rate=8000 from the fmt chunk
   - Expected: sr equals `8000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports sample_rate=8000 from the fmt chunk")
val r = decode_wav(KAT_PCM16_8KHZ_ONE_SAMPLE)
var sr: i64 = -1
if val Ok(a) = r:
    sr = a.sample_rate
expect(sr).to_equal(8000)
```

</details>

#### reports channels=1 from the fmt chunk

- reports channels=1 from the fmt chunk
   - Expected: ch equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports channels=1 from the fmt chunk")
val r = decode_wav(KAT_PCM16_8KHZ_ONE_SAMPLE)
var ch: i64 = -1
if val Ok(a) = r:
    ch = a.channels
expect(ch).to_equal(1)
```

</details>

#### unknown chunk between fmt and data is skipped by size, not misread

#### still decodes the sample after a spliced-in 4-byte unknown chunk

- still decodes the sample after a spliced-in 4-byte unknown chunk
   - Expected: got equals `[0.5]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still decodes the sample after a spliced-in 4-byte unknown chunk")
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

- rejects bytes missing the RIFF tag with a clear Err
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects bytes missing the RIFF tag with a clear Err")
val bad: [u8] = [88u8, 88u8, 88u8, 88u8, 0u8, 0u8, 0u8, 0u8, 87u8, 65u8, 86u8, 69u8]
val r = decode_wav(bad)
var has_marker = false
if val Err(e) = r:
    has_marker = e.contains("RIFF")
expect(has_marker).to_equal(true)
```

</details>

#### rejects an unsupported audio_format/bits combination (8-bit PCM) with a clear Err

- rejects an unsupported audio_format/bits combination (8-bit PCM) with a clear Err
   - Expected: has_marker is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an unsupported audio_format/bits combination (8-bit PCM) with a clear Err")
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

- round-trips [0.0, 0.5, -0.5, 1.0] to [0.0, 0.5, -0.5, 32767/32768]
   - Expected: got equals `[0.0, 0.5, -0.5, 0.999969482421875]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips [0.0, 0.5, -0.5, 1.0] to [0.0, 0.5, -0.5, 32767/32768]")
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

- round-trips [0.0, 0.5, -0.5, 1.0] exactly
   - Expected: got equals `[0.0, 0.5, -0.5, 1.0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("round-trips [0.0, 0.5, -0.5, 1.0] exactly")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering wav_decode decode_wav, wav_decode / wav_encode round-trip.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5cfa69bc4a4f140234c666b8961900c9a49d6bf3b5bed037a8dfd49171e8a085`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5cfa69bc4a4f140234c666b8961900c9a49d6bf3b5bed037a8dfd49171e8a085`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5cfa69bc4a4f140234c666b8961900c9a49d6bf3b5bed037a8dfd49171e8a085`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/audio/wav_decode_spec.spl
mirror: doc/06_spec/01_unit/lib/common/audio/wav_decode_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/audio/wav_decode_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/audio/wav_decode_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/audio/wav_decode_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/audio/wav_decode_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes one 0x4000 PCM16 sample to exactly 0.5' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/audio/wav_decode_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports sample_rate=8000 from the fmt chunk' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/audio/wav_decode_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports channels=1 from the fmt chunk' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
