# Zstd Bit Round Trip Specification

> Tests covering zstd bit writer/reader round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Bit Round Trip Specification

## Scenarios

### zstd bit writer/reader round-trip

#### msb writer + msb backward reader recover the same value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- msb writer + msb backward reader recover the same value
   - Expected: w1_res.is_err() is false
   - Expected: bytes_res.is_err() is false
   - Expected: r0_res.is_err() is false
   - Expected: v_res.is_err() is false
   - Expected: v equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("msb writer + msb backward reader recover the same value")
val w0 = zstd_bit_writer_new()
val w1_res = zstd_bit_writer_append_msb(w0, 4u64, 3)
expect(w1_res.is_err()).to_equal(false)
val w1 = w1_res.unwrap()
val bytes_res = zstd_bit_writer_finish(w1)
expect(bytes_res.is_err()).to_equal(false)
val bytes = bytes_res.unwrap()
val r0_res = zstd_msb_bits_init(bytes, 0, bytes.len())
expect(r0_res.is_err()).to_equal(false)
val r0 = r0_res.unwrap()
val v_res = zstd_msb_bits_read(r0, 3)
expect(v_res.is_err()).to_equal(false)
val (v, _r, _p) = v_res.unwrap()
expect(v).to_equal(4)
```

</details>

#### lsb writer + msb backward reader recover the same value

- lsb writer + msb backward reader recover the same value
   - Expected: v equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lsb writer + msb backward reader recover the same value")
val w0 = zstd_bit_writer_new()
val w1_res = zstd_bit_writer_append_lsb(w0, 4u64, 3)
val w1 = w1_res.unwrap()
val bytes = zstd_bit_writer_finish(w1).unwrap()
val r0 = zstd_msb_bits_init(bytes, 0, bytes.len()).unwrap()
val (v, _r, _p) = zstd_msb_bits_read(r0, 3).unwrap()
expect(v).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/zstd_bit_round_trip_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering zstd bit writer/reader round-trip.
- zstd bit writer/reader round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `daab2d81ae087ed76ac08188a63eabaeeb3dd71a19ed286fdc8a3c5704296252`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `daab2d81ae087ed76ac08188a63eabaeeb3dd71a19ed286fdc8a3c5704296252`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `daab2d81ae087ed76ac08188a63eabaeeb3dd71a19ed286fdc8a3c5704296252`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/lib/common/zstd_bit_round_trip_spec.spl
mirror: doc/06_spec/unit/lib/common/zstd_bit_round_trip_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/zstd_bit_round_trip_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/zstd_bit_round_trip_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/zstd_bit_round_trip_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/zstd_bit_round_trip_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'msb writer + msb backward reader recover the same value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/zstd_bit_round_trip_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lsb writer + msb backward reader recover the same value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
