# Simpleos Evidence Receipt V1 Codec Specification

> Tests covering SimpleOS evidence receipt v1 codec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Evidence Receipt V1 Codec Specification

## Scenarios

### SimpleOS evidence receipt v1 codec

#### round trips every identity performance and signed outcome field

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round trips every identity performance and signed outcome field


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round trips every identity performance and signed outcome field")
val encoded = encode_simpleos_evidence_receipt_v1(_codec_receipt())
assert_true(encoded.ok)
val decoded = decode_simpleos_evidence_receipt_v1(encoded.bytes)
assert_true(decoded.ok)
assert_equal(decoded.value.receipt_id, "receipt-codec-1")
assert_equal(decoded.value.environment, SimpleOsEvidenceEnvironment.NativeHost)
assert_equal(decoded.value.steps[0].exit_code, 0)
assert_equal(decoded.value.performance_workload, "warm_server_startup")
assert_equal(decoded.value.performance_unit, "microseconds_milli")
assert_equal(decoded.value.performance_warmup_count, 3)
assert_equal(decoded.value.performance_cpu_identity, "test-cpu-1")
assert_equal(decoded.value.performance_frequency_hz, 3000000000)
assert_equal(decoded.value.performance_noise_profile, "isolated-core")
assert_true(decoded.value.performance_comparable)
assert_equal(decoded.value.performance_samples.len(), 10)
assert_equal(decoded.value.performance_samples[9].metric_value_milli, 125009)
assert_equal(decoded.value.performance_samples[9].elapsed_us, 1009)
assert_equal(decoded.value.performance_samples[9].max_rss_bytes, 1048585)
```

</details>

#### rejects an invalid envelope truncation and trailing bytes

- rejects an invalid envelope truncation and trailing bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an invalid envelope truncation and trailing bytes")
val encoded = encode_simpleos_evidence_receipt_v1(_codec_receipt())
var bad_magic = encoded.bytes
bad_magic[0] = 0u8
assert_false(decode_simpleos_evidence_receipt_v1(bad_magic).ok)
var truncated: [u8] = []
var i: i64 = 0
while i + 1 < encoded.bytes.len():
    truncated.push(encoded.bytes[i])
    i = i + 1
assert_false(decode_simpleos_evidence_receipt_v1(truncated).ok)
var trailing = encoded.bytes
trailing.push(0u8)
assert_false(decode_simpleos_evidence_receipt_v1(trailing).ok)
```

</details>

#### defines signing bytes that omit only the self-referential signature field

- defines signing bytes that omit only the self-referential signature field


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines signing bytes that omit only the self-referential signature field")
val receipt = _codec_receipt()
val full = encode_simpleos_evidence_receipt_v1(receipt)
val signing = encode_simpleos_evidence_receipt_v1_signing_bytes(receipt)
assert_true(full.ok)
assert_true(signing.ok)
assert_equal(full.bytes.len() - signing.bytes.len(), 4 + receipt.signature.len())
var unsigned = receipt
unsigned.signature = ""
assert_false(encode_simpleos_evidence_receipt_v1(unsigned).ok)
assert_true(encode_simpleos_evidence_receipt_v1_signing_bytes(unsigned).ok)
```

</details>

#### rejects non printable text before wire admission

- rejects non printable text before wire admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non printable text before wire admission")
var receipt = _codec_receipt()
receipt.owner = "owner\nforged"
assert_false(encode_simpleos_evidence_receipt_v1(receipt).ok)
```

</details>

#### rejects failed evidence steps before wire admission

- rejects failed evidence steps before wire admission


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects failed evidence steps before wire admission")
var receipt = _codec_receipt()
receipt.steps[0].exit_code = 9
assert_false(encode_simpleos_evidence_receipt_v1(receipt).ok)
receipt = _codec_receipt()
receipt.steps[0].outcome = "failed"
assert_false(encode_simpleos_evidence_receipt_v1(receipt).ok)
```

</details>

#### rejects an unknown comparable boolean discriminant

- rejects an unknown comparable boolean discriminant


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unknown comparable boolean discriminant")
val encoded = encode_simpleos_evidence_receipt_v1(_codec_receipt())
var corrupted = encoded.bytes
# The comparable flag immediately precedes the sample count. Locate it
# from the fixed 10-sample tail without duplicating all variable offsets.
val tail_after_flag = 4 + 10 * 32 + 16 +
    (4 + "measurement-owner".len()) +
    (4 + "independent-reviewer".len()) +
    (4 + "test-key-1".len()) +
    (4 + "test-signature".len())
val flag_offset = corrupted.len() - tail_after_flag - 1
corrupted[flag_offset] = 2u8
assert_false(decode_simpleos_evidence_receipt_v1(corrupted).ok)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/structural/simpleos_evidence_receipt_v1_codec_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS evidence receipt v1 codec.
- SimpleOS evidence receipt v1 codec

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

- Canonical SPipe generation for source `b8dea4c28ae4600eb963594c87fab46c66f6707972df3da8a8f65d81121714f9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b8dea4c28ae4600eb963594c87fab46c66f6707972df3da8a8f65d81121714f9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b8dea4c28ae4600eb963594c87fab46c66f6707972df3da8a8f65d81121714f9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/structural/simpleos_evidence_receipt_v1_codec_spec.spl
mirror: doc/06_spec/01_unit/lib/common/structural/simpleos_evidence_receipt_v1_codec_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/structural/simpleos_evidence_receipt_v1_codec_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/structural/simpleos_evidence_receipt_v1_codec_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/structural/simpleos_evidence_receipt_v1_codec_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round trips every identity performance and signed outcome field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/structural/simpleos_evidence_receipt_v1_codec_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an invalid envelope truncation and trailing bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/structural/simpleos_evidence_receipt_v1_codec_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines signing bytes that omit only the self-referential signature field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
