# Serialization Multibyte Specification

> Tests covering serialize_string / crc32_calculate multi-byte.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serialization Multibyte Specification

## Scenarios

### serialize_string / crc32_calculate multi-byte

#### café serializes to its exact 4-byte-length-prefixed UTF-8 wire bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- café serializes to its exact 4-byte-length-prefixed UTF-8 wire bytes
   - Expected: encoded.len() equals `9`
   - Expected: encoded[3] equals `5`
   - Expected: encoded[4] equals `99`
   - Expected: encoded[5] equals `97`
   - Expected: encoded[6] equals `102`
   - Expected: encoded[7] equals `195`
   - Expected: encoded[8] equals `169`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("café serializes to its exact 4-byte-length-prefixed UTF-8 wire bytes")
val encoded = serialize_string("café")
# 4-byte big-endian length prefix (0,0,0,5) + 5 payload bytes
expect(encoded.len()).to_equal(9)
expect(encoded[3]).to_equal(5)
expect(encoded[4]).to_equal(99)
expect(encoded[5]).to_equal(97)
expect(encoded[6]).to_equal(102)
expect(encoded[7]).to_equal(195)
expect(encoded[8]).to_equal(169)
```

</details>

#### crc32_calculate does not crash on multi-byte input and differs from an unrelated ASCII string's CRC

- crc32_calculate does not crash on multi-byte input and differs from an unrelated ASCII string's CRC


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("crc32_calculate does not crash on multi-byte input and differs from an unrelated ASCII string's CRC")
val crc_ascii = crc32_calculate("hello")
val crc_mb = crc32_calculate("café")
expect(crc_mb == crc_ascii).to_be(false)
```

</details>

#### pure ASCII serialize_string is unaffected (regression guard)

- pure ASCII serialize_string is unaffected (regression guard)
   - Expected: encoded.len() equals `6`
   - Expected: encoded[3] equals `2`
   - Expected: encoded[4] equals `104`
   - Expected: encoded[5] equals `105`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pure ASCII serialize_string is unaffected (regression guard)")
val encoded = serialize_string("hi")
expect(encoded.len()).to_equal(6)
expect(encoded[3]).to_equal(2)
expect(encoded[4]).to_equal(104)
expect(encoded[5]).to_equal(105)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/kafka/serialization_multibyte_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering serialize_string / crc32_calculate multi-byte.
- serialize_string / crc32_calculate multi-byte

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `97f2fbd42d8692a243759b53391dedb5da9ea3609563114e8f312f148f81af28`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `97f2fbd42d8692a243759b53391dedb5da9ea3609563114e8f312f148f81af28`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `97f2fbd42d8692a243759b53391dedb5da9ea3609563114e8f312f148f81af28`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/nogc_sync_mut/kafka/serialization_multibyte_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/kafka/serialization_multibyte_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/kafka/serialization_multibyte_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/kafka/serialization_multibyte_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/kafka/serialization_multibyte_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/kafka/serialization_multibyte_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'café serializes to its exact 4-byte-length-prefixed UTF-8 wire bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/kafka/serialization_multibyte_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'crc32_calculate does not crash on multi-byte input and differs from an unrelated ASCII string's CRC' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/kafka/serialization_multibyte_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pure ASCII serialize_string is unaffected (regression guard)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
