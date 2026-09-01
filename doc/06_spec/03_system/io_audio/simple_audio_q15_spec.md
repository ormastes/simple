# simple_audio_q15_spec

> Q15 audio work has deterministic bounds, convolution, checksum, and parity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simple_audio_q15_spec

Q15 audio work has deterministic bounds, convolution, checksum, and parity.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/io_audio/simple_audio_q15_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Q15 audio work has deterministic bounds, convolution, checksum, and parity.

## Scenarios

### Simple audio Q15 work

#### rejects empty and oversized work before dispatch

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects empty and oversized work before dispatch
   - Expected: simple_audio_q15_work_status([], [32768u32]) equals `empty-audio-work`
   - Expected: simple_audio_q15_work_status([32768u32], []) equals `empty-audio-work`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects empty and oversized work before dispatch")
expect(simple_audio_q15_work_status([], [32768u32])).to_equal("empty-audio-work")
expect(simple_audio_q15_work_status([32768u32], [])).to_equal("empty-audio-work")
```

</details>

#### computes signed Q15 convolution with a deterministic checksum

- computes signed Q15 convolution with a deterministic checksum
   - Expected: result.len() equals `4`
   - Expected: simple_audio_q15_decode(result[0]) equals `16384`
   - Expected: simple_audio_q15_decode(result[1]) equals `16384`
   - Expected: simple_audio_q15_decode(result[2]) equals `0`
   - Expected: simple_audio_q15_decode(result[3]) equals `-2048`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes signed Q15 convolution with a deterministic checksum")
val result = simple_audio_q15_convolve_reference([32768u32, 16384u32, 4294959104u32], [16384u32, 8192u32])
expect(result.len()).to_equal(4)
expect(simple_audio_q15_decode(result[0])).to_equal(16384)
expect(simple_audio_q15_decode(result[1])).to_equal(16384)
expect(simple_audio_q15_decode(result[2])).to_equal(0)
expect(simple_audio_q15_decode(result[3])).to_equal(-2048)
expect(simple_audio_q15_checksum(result)).to_be_greater_than(0)
```

</details>

#### detects exact and divergent device readback

- detects exact and divergent device readback
   - Expected: simple_audio_q15_max_error_millionths(reference, reference) equals `0`
   - Expected: simple_audio_q15_max_error_millionths(reference, [1u32, 2u32]) equals `1000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects exact and divergent device readback")
val reference = [1u32, 2u32, 3u32]
expect(simple_audio_q15_max_error_millionths(reference, reference)).to_equal(0)
expect(simple_audio_q15_max_error_millionths(reference, [1u32, 2u32])).to_equal(1000000)
expect(simple_audio_q15_max_error_millionths(reference, [1u32, 2u32, 100u32])).to_be_greater_than(10)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-001`
- `REQ-004`
- `REQ-005`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3ae48f52248d57eea08ead90604dec3f77a8de60786054d397daaa2fc2c83020`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3ae48f52248d57eea08ead90604dec3f77a8de60786054d397daaa2fc2c83020`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3ae48f52248d57eea08ead90604dec3f77a8de60786054d397daaa2fc2c83020`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/io_audio/simple_audio_q15_spec.spl
mirror: doc/06_spec/03_system/io_audio/simple_audio_q15_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/03_system/io_audio/simple_audio_q15_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/io_audio/simple_audio_q15_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/io_audio/simple_audio_q15_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/io_audio/simple_audio_q15_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/io_audio/simple_audio_q15_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects empty and oversized work before dispatch' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/io_audio/simple_audio_q15_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes signed Q15 convolution with a deterministic checksum' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/io_audio/simple_audio_q15_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects exact and divergent device readback' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
