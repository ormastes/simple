# Gzip Validate Crc Isize Specification

> Tests covering gzip_validate — CRC32 + ISIZE trailer verification.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Gzip Validate Crc Isize Specification

## Scenarios

### gzip_validate — CRC32 + ISIZE trailer verification

#### REPRODUCE: rejects a corrupted deflate-body byte (previously a false pass)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- REPRODUCE: rejects a corrupted deflate-body byte (previously a false pass)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REPRODUCE: rejects a corrupted deflate-body byte (previously a false pass)")
var z = gzip_compress(_sample_data(100), 6)
val mid = z.len() / 2
z[mid] = (z[mid] + 1) % 256
assert_false(gzip_validate(z))
```

</details>

#### still accepts a valid roundtrip (no false positives)

- still accepts a valid roundtrip (no false positives)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still accepts a valid roundtrip (no false positives)")
val z = gzip_compress(_sample_data(400), 6)
assert_true(gzip_validate(z))
val back = gzip_decompress(z) ?? []
assert_equal(back.len(), 400)
```

</details>

#### accepts a valid empty-payload gzip stream

- accepts a valid empty-payload gzip stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a valid empty-payload gzip stream")
var empty: [u8] = []
val z = gzip_compress(empty, 6)
assert_true(gzip_validate(z))
```

</details>

#### rejects corrupted CRC trailer bytes

- rejects corrupted CRC trailer bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects corrupted CRC trailer bytes")
var z = gzip_compress(_sample_data(50), 6)
val crc_offset = z.len() - 8
z[crc_offset] = z[crc_offset] ^ 0x01
assert_false(gzip_validate(z))
```

</details>

#### rejects a corrupted ISIZE trailer

- rejects a corrupted ISIZE trailer


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a corrupted ISIZE trailer")
var z = gzip_compress(_sample_data(50), 6)
val isize_offset = z.len() - 4
z[isize_offset] = z[isize_offset] ^ 0x01
assert_false(gzip_validate(z))
```

</details>

#### rejects a truncated trailer (footer parse fails)

- rejects a truncated trailer (footer parse fails)


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a truncated trailer (footer parse fails)")
var z = gzip_compress(_sample_data(50), 6)
var truncated: [u8] = []
var i = 0
while i < z.len() - 3:
    truncated.push(z[i])
    i = i + 1
assert_false(gzip_validate(truncated))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/compression/gzip_validate_crc_isize_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gzip_validate — CRC32 + ISIZE trailer verification.
- gzip_validate — CRC32 + ISIZE trailer verification

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

- Canonical SPipe generation for source `65f408f5c95885b8ea22780da482cc98812408ec2170398047156e0f983fd688`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `65f408f5c95885b8ea22780da482cc98812408ec2170398047156e0f983fd688`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `65f408f5c95885b8ea22780da482cc98812408ec2170398047156e0f983fd688`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_sync_mut/compression/gzip_validate_crc_isize_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/compression/gzip_validate_crc_isize_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/compression/gzip_validate_crc_isize_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/compression/gzip_validate_crc_isize_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/compression/gzip_validate_crc_isize_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'REPRODUCE: rejects a corrupted deflate-body byte (previously a false pass)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/compression/gzip_validate_crc_isize_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'still accepts a valid roundtrip (no false positives)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/compression/gzip_validate_crc_isize_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a valid empty-payload gzip stream' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
