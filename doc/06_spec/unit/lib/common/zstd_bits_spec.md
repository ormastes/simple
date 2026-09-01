# Zstd Bits Specification

> Tests covering zstd backward bit helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Zstd Bits Specification

## Scenarios

### zstd backward bit helpers

#### reads little-endian integers with bounded truncation checks

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads little-endian integers with bounded truncation checks
   - Expected: word.is_err() is false
   - Expected: word.unwrap() equals `0x12345678u32`
   - Expected: long.is_err() is false
   - Expected: long.unwrap() equals `0x0102030405060708u64`
   - Expected: truncated.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads little-endian integers with bounded truncation checks")
val data = [
    0x78u8, 0x56u8, 0x34u8, 0x12u8,
    0x08u8, 0x07u8, 0x06u8, 0x05u8,
    0x04u8, 0x03u8, 0x02u8, 0x01u8
]
val word = zstd_read_u32_le(data, 0)
expect(word.is_err()).to_equal(false)
expect(word.unwrap()).to_equal(0x12345678u32)
val long = zstd_read_u64_le(data, 4)
expect(long.is_err()).to_equal(false)
expect(long.unwrap()).to_equal(0x0102030405060708u64)
val truncated = zstd_read_u32_le(data, 9)
expect(truncated.is_err()).to_equal(true)
_expect_compression_error(truncated.unwrap_err(), "TruncatedInput", "4 bytes")
```

</details>

#### peeks and consumes a reverse reservoir across the tail sentinel

- peeks and consumes a reverse reservoir across the tail sentinel
   - Expected: init.is_err() is false
   - Expected: zstd_bits_remaining(reader) equals `20`
   - Expected: low.is_err() is false
   - Expected: low.unwrap() equals `0x07u32`
   - Expected: after_low.is_err() is false
   - Expected: middle.is_err() is false
   - Expected: middle_byte equals `0xCDu32`
   - Expected: high.is_err() is false
   - Expected: high.unwrap() equals `0xABu32`
   - Expected: zstd_bits_remaining(after_middle) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("peeks and consumes a reverse reservoir across the tail sentinel")
val data = [0xABu8, 0xCDu8, 0x17u8]
val init = zstd_bits_init(data, 0, data.len())
expect(init.is_err()).to_equal(false)
val reader = init.unwrap()
expect(zstd_bits_remaining(reader)).to_equal(20)
val low = zstd_bits_peek(reader, 4)
expect(low.is_err()).to_equal(false)
expect(low.unwrap()).to_equal(0x07u32)
val after_low = zstd_bits_consume(reader, 4)
expect(after_low.is_err()).to_equal(false)
val middle = zstd_bits_read(after_low.unwrap(), 8)
expect(middle.is_err()).to_equal(false)
val (middle_byte, after_middle) = middle.unwrap()
expect(middle_byte).to_equal(0xCDu32)
val high = zstd_bits_peek(after_middle, 8)
expect(high.is_err()).to_equal(false)
expect(high.unwrap()).to_equal(0xABu32)
expect(zstd_bits_remaining(after_middle)).to_equal(8)
```

</details>

#### fails closed on a missing tail mark

- fails closed on a missing tail mark
   - Expected: init.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed on a missing tail mark")
val init = zstd_bits_init([0xAAu8, 0x00u8], 0, 2)
expect(init.is_err()).to_equal(true)
_expect_compression_error(init.unwrap_err(), "CorruptStream", "end mark")
```

</details>

#### fails closed when the caller asks for more bits than remain

- fails closed when the caller asks for more bits than remain
   - Expected: init.is_err() is false
   - Expected: full.is_err() is false
   - Expected: truncated.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fails closed when the caller asks for more bits than remain")
val init = zstd_bits_init([0x55u8, 0x01u8], 0, 2)
expect(init.is_err()).to_equal(false)
val reader = init.unwrap()
val full = zstd_bits_read(reader, 8)
expect(full.is_err()).to_equal(false)
val (_byte, empty) = full.unwrap()
val truncated = zstd_bits_peek(empty, 1)
expect(truncated.is_err()).to_equal(true)
_expect_compression_error(truncated.unwrap_err(), "TruncatedInput", "bitstream bits")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/zstd_bits_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering zstd backward bit helpers.
- zstd backward bit helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `b47b756d83627024cd0941ee6b20a25f42b116681b0fb96cc1fae9006cac5b5f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b47b756d83627024cd0941ee6b20a25f42b116681b0fb96cc1fae9006cac5b5f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b47b756d83627024cd0941ee6b20a25f42b116681b0fb96cc1fae9006cac5b5f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/zstd_bits_spec.spl
mirror: doc/06_spec/unit/lib/common/zstd_bits_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/zstd_bits_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/zstd_bits_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/zstd_bits_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/zstd_bits_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads little-endian integers with bounded truncation checks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/zstd_bits_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'peeks and consumes a reverse reservoir across the tail sentinel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/zstd_bits_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on a missing tail mark' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
