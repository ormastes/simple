# Audio/media evidence profile (E7 domain profile)

> For QA authors capturing audio evidence: this spec proves the `AudioSampleSet`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Audio/media evidence profile (E7 domain profile)

For QA authors capturing audio evidence: this spec proves the `AudioSampleSet`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/spec/evidence/audio_profile_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

For QA authors capturing audio evidence: this spec proves the `AudioSampleSet`
profile — validity rules on samples/format, derived duration, scaled RMS/peak
levels and silence ratio — and its fail-closed projection into
`CanonicalEvidence`. Audience: reviewers who must trust audio-level claims
without decoding the raw buffer.

## Scenarios

### Audio evidence profile

#### rejects an empty sample set as not a real capture

- Build a sample set with no samples
- Verify it is rejected as invalid
   - Expected: audio_sample_set_is_valid(empty) is false
- Verify converting it to evidence fails to parse instead of emitting a zero-valued reading
   - Expected: evidence.parse_ok is false
   - Expected: evidence.nodes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SSPEC-EVD-007-AUDIO
step("Build a sample set with no samples")
val empty = AudioSampleSet(channel_count: 2, sample_rate_hz: 8000, bit_depth: 16, samples: [])

step("Verify it is rejected as invalid")
expect(audio_sample_set_is_valid(empty)).to_equal(false)

step("Verify converting it to evidence fails to parse instead of emitting a zero-valued reading")
val evidence = audio_to_evidence(empty, "audio/capture")
expect(evidence.parse_ok).to_equal(false)
expect(evidence.nodes.len()).to_equal(0)
```

</details>

#### rejects a non-positive sample rate

- rejects a non-positive sample rate
- Build a sample set with sample_rate_hz of 0
   - Expected: audio_sample_set_is_valid(zero_rate) is false
   - Expected: evidence.parse_ok is false
- Build a sample set with a negative sample_rate_hz
   - Expected: audio_sample_set_is_valid(negative_rate) is false
   - Expected: negative_evidence.parse_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a non-positive sample rate")
step("Build a sample set with sample_rate_hz of 0")
val zero_rate = AudioSampleSet(channel_count: 2, sample_rate_hz: 0, bit_depth: 16, samples: [1, 2])
expect(audio_sample_set_is_valid(zero_rate)).to_equal(false)
val evidence = audio_to_evidence(zero_rate, "audio/capture")
expect(evidence.parse_ok).to_equal(false)

step("Build a sample set with a negative sample_rate_hz")
val negative_rate = AudioSampleSet(channel_count: 2, sample_rate_hz: -1, bit_depth: 16, samples: [1, 2])
expect(audio_sample_set_is_valid(negative_rate)).to_equal(false)
val negative_evidence = audio_to_evidence(negative_rate, "audio/capture")
expect(negative_evidence.parse_ok).to_equal(false)
```

</details>

#### rejects a zero channel count

- rejects a zero channel count
- Build a sample set with channel_count of 0
- Verify it is rejected as invalid and fails to parse
   - Expected: audio_sample_set_is_valid(zero_channels) is false
   - Expected: evidence.parse_ok is false
   - Expected: evidence.nodes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a zero channel count")
step("Build a sample set with channel_count of 0")
val zero_channels = AudioSampleSet(channel_count: 0, sample_rate_hz: 8000, bit_depth: 16, samples: [1, 2])

step("Verify it is rejected as invalid and fails to parse")
expect(audio_sample_set_is_valid(zero_channels)).to_equal(false)
val evidence = audio_to_evidence(zero_channels, "audio/capture")
expect(evidence.parse_ok).to_equal(false)
expect(evidence.nodes.len()).to_equal(0)
```

</details>

#### derives duration from the actual sample count, never an asserted field

- derives duration from the actual sample count, never an asserted field
- Compute duration for a stereo 8kHz capture of 8 interleaved samples (4 frames)
- Verify duration matches frames/rate, not any value the caller could assert independently
   - Expected: duration equals `0`
- Compute duration for a longer capture where the math yields a nonzero result
   - Expected: longer_duration equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("derives duration from the actual sample count, never an asserted field")
step("Compute duration for a stereo 8kHz capture of 8 interleaved samples (4 frames)")
val duration = audio_duration_ms(8, 8000, 2)

step("Verify duration matches frames/rate, not any value the caller could assert independently")
expect(duration).to_equal(0)

step("Compute duration for a longer capture where the math yields a nonzero result")
val longer_duration = audio_duration_ms(16000, 8000, 2)
expect(longer_duration).to_equal(1000)
```

</details>

#### computes RMS of an all-zero buffer as exactly zero

- computes RMS of an all-zero buffer as exactly zero
- Build an all-silent buffer
- Verify RMS is exactly zero, not merely close to zero
   - Expected: audio_rms_scaled(silence, 1) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("computes RMS of an all-zero buffer as exactly zero")
step("Build an all-silent buffer")
val silence: [i64] = [0, 0, 0, 0, 0, 0]

step("Verify RMS is exactly zero, not merely close to zero")
expect(audio_rms_scaled(silence, 1)).to_equal(0)
```

</details>

#### computes RMS of a full-scale square wave close to its peak

- computes RMS of a full-scale square wave close to its peak
- Build a symmetric square wave alternating between +peak and -peak
- Verify the computed RMS equals the computed peak (a square wave's RMS is its peak)
   - Expected: rms equals `peak`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("computes RMS of a full-scale square wave close to its peak")
step("Build a symmetric square wave alternating between +peak and -peak")
val peak_value: i64 = 5000
val square: [i64] = [peak_value, 0 - peak_value, peak_value, 0 - peak_value, peak_value, 0 - peak_value]

step("Verify the computed RMS equals the computed peak (a square wave's RMS is its peak)")
val rms = audio_rms_scaled(square, 1)
val peak = audio_peak_scaled(square)
expect(rms).to_equal(peak)
```

</details>

#### reports silence ratio in parts-per-thousand from the actual samples

- reports silence ratio in parts-per-thousand from the actual samples
- Build a buffer where half the samples are below the silence threshold
- Verify the silence ratio is exactly 500 permille (half)
   - Expected: audio_silence_ratio_permille(mixed, 0) equals `500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports silence ratio in parts-per-thousand from the actual samples")
step("Build a buffer where half the samples are below the silence threshold")
val mixed: [i64] = [0, 0, 0, 5000, 5000, 5000]

step("Verify the silence ratio is exactly 500 permille (half)")
expect(audio_silence_ratio_permille(mixed, 0)).to_equal(500)
```

</details>

#### feeds a captured buffer into compare_evidence against a closed oracle

- feeds a captured buffer into compare_evidence against a closed oracle
- Convert a valid stereo capture to canonical evidence
   - Expected: evidence.parse_ok is true
- Build a closed oracle checking format fields exactly and RMS within a stated tolerance
- Verify the evidence passes the closed oracle
   - Expected: result.status equals `EvidenceStatus.passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("feeds a captured buffer into compare_evidence against a closed oracle")
step("Convert a valid stereo capture to canonical evidence")
val evidence = audio_to_evidence(stereo_capture(), "audio/capture")
expect(evidence.parse_ok).to_equal(true)

step("Build a closed oracle checking format fields exactly and RMS within a stated tolerance")
val expected_rms = audio_rms_scaled(stereo_capture().samples, 1)
val expected_peak = audio_peak_scaled(stereo_capture().samples)
val expected_duration = audio_duration_ms(stereo_capture().samples.len(), 8000, 2)
val expected_silence = audio_silence_ratio_permille(stereo_capture().samples, 0)
val oracle: OracleSpec = oracle_spec(
    "audio/capture",
    [
        check_exact("audio.channel_count", "2"),
        check_exact("audio.sample_rate_hz", "8000"),
        check_exact("audio.bit_depth", "16"),
        check_exact("audio.duration_ms", "{expected_duration}"),
        check_exact("audio.peak", "{expected_peak}"),
        check_exact("audio.silence_ratio_permille", "{expected_silence}"),
        check_numeric_tolerance(
            "audio.rms", "{expected_rms}", 5,
            "RMS is deterministic for this fixed buffer; a small tolerance absorbs any future integer-sqrt rounding change"
        )
    ]
)

step("Verify the evidence passes the closed oracle")
val result = compare_evidence(evidence, oracle)
expect(result.status).to_equal(EvidenceStatus.passed)
```

</details>

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
- `REQ-SSPEC-EVD-007-AUDIO`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `abdcd2a5f9ff2396881fd4d83c75ffbf3ceff3cab6b734cf0de71794853155db`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `abdcd2a5f9ff2396881fd4d83c75ffbf3ceff3cab6b734cf0de71794853155db`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `abdcd2a5f9ff2396881fd4d83c75ffbf3ceff3cab6b734cf0de71794853155db`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/spec/evidence/audio_profile_spec.spl
mirror: doc/06_spec/01_unit/lib/common/spec/evidence/audio_profile_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/spec/evidence/audio_profile_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/spec/evidence/audio_profile_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/spec/evidence/audio_profile_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/spec/evidence/audio_profile_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives duration from the actual sample count, never an asserted field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/spec/evidence/audio_profile_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes RMS of an all-zero buffer as exactly zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/spec/evidence/audio_profile_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes RMS of a full-scale square wave close to its peak' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
