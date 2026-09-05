# Lz4 Empty Payload Roundtrip Specification

> Tests covering lz4 empty-payload frame round-trip, empty-payload self-round-trip across lz4 framing options (detection).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lz4 Empty Payload Roundtrip Specification

## Scenarios

### lz4 empty-payload frame round-trip

#### round-trips an empty payload through the public compress facade

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### emits header plus EndMark only, never a zero-length data block

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val options = default_compression_options(CompressionCodec.lz4)
val encoded = lz4_compress_frame([], options)
# 4 magic + FLG + BD + HC + 4 EndMark = 11 bytes, no block size word.
expect(encoded.len()).to_equal(11)
val decoded = lz4_decompress_frame(encoded)
expect(decoded.is_err()).to_equal(false)
expect(decoded.unwrap().len()).to_equal(0)
```

</details>

### empty-payload self-round-trip across lz4 framing options (detection)

#### every lz4 framing option variant decodes its own empty-payload frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Generalises the class: the encoder must never emit a shape its own
# decoder rejects, under ANY combination of checksum / content-size
# framing options, not just the default one the original bug hit.
val base = default_compression_options(CompressionCodec.lz4)
var variants: [CompressionOptions] = []
variants = variants.push(base)
variants = variants.push(CompressionOptions(
    base.codec, base.level, true, base.block_mode,
    base.dictionary_bytes, base.dictionary_id, nil))
variants = variants.push(CompressionOptions(
    base.codec, base.level, false, base.block_mode,
    base.dictionary_bytes, base.dictionary_id, 0))
variants = variants.push(CompressionOptions(
    base.codec, base.level, true, base.block_mode,
    base.dictionary_bytes, base.dictionary_id, 0))

var failures = 0
for opts in variants:
    val encoded = lz4_compress_frame([], opts)
    val decoded = lz4_decompress_frame(encoded)
    if decoded.is_err():
        failures = failures + 1
    else:
        if decoded.unwrap().len() != 0:
            failures = failures + 1
expect(failures).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/lz4_empty_payload_roundtrip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering lz4 empty-payload frame round-trip, empty-payload self-round-trip across lz4 framing options (detection).
- lz4 empty-payload frame round-trip
- empty-payload self-round-trip across lz4 framing options (detection)

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dd6013d47ba944b82dbe2eba4f5eee9150f7f40e1b549e190780526d7d727c42`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dd6013d47ba944b82dbe2eba4f5eee9150f7f40e1b549e190780526d7d727c42`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dd6013d47ba944b82dbe2eba4f5eee9150f7f40e1b549e190780526d7d727c42`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/01_unit/lib/common/compress/lz4_empty_payload_roundtrip_spec.spl
mirror: doc/06_spec/01_unit/lib/common/compress/lz4_empty_payload_roundtrip_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=70 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/compress/lz4_empty_payload_roundtrip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/compress/lz4_empty_payload_roundtrip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/compress/lz4_empty_payload_roundtrip_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/common/compress/lz4_empty_payload_roundtrip_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/compress/lz4_empty_payload_roundtrip_spec.spl:32:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'round-trips an empty payload through the public compress facade' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/compress/lz4_empty_payload_roundtrip_spec.spl:42:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'emits header plus EndMark only, never a zero-length data block' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/common/compress/lz4_empty_payload_roundtrip_spec.spl:53:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'every lz4 framing option variant decodes its own empty-payload frame' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
