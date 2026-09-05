# Utf32 Encode Byte Guard Specification

> Tests covering utf32 byte encoding guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Utf32 Encode Byte Guard Specification

## Scenarios

### utf32 byte encoding guards

#### keeps valid little-endian serialization

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps valid little-endian serialization


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid little-endian serialization")
assert_equal(utf32_to_bytes_le([0x41]), [0x41, 0x00, 0x00, 0x00])
```

</details>

#### keeps valid big-endian serialization

- keeps valid big-endian serialization


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps valid big-endian serialization")
assert_equal(utf32_to_bytes_be([0x41]), [0x00, 0x00, 0x00, 0x41])
```

</details>

#### serializes negative scalars as replacement

- serializes negative scalars as replacement


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes negative scalars as replacement")
assert_equal(utf32_from_bytes_le(utf32_to_bytes_le([-1])), [0xFFFD])
```

</details>

#### serializes above-range scalars as replacement

- serializes above-range scalars as replacement


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serializes above-range scalars as replacement")
assert_equal(utf32_from_bytes_be(utf32_to_bytes_be([0x110000])), [0xFFFD])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/encoding/utf32_encode_byte_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering utf32 byte encoding guards.
- utf32 byte encoding guards

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

- Canonical SPipe generation for source `4c7878d847d28f8c669d2cd7fa53bdf2b9128d72f40d9ede28fb70f23acd0627`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4c7878d847d28f8c669d2cd7fa53bdf2b9128d72f40d9ede28fb70f23acd0627`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4c7878d847d28f8c669d2cd7fa53bdf2b9128d72f40d9ede28fb70f23acd0627`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/encoding/utf32_encode_byte_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/encoding/utf32_encode_byte_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/encoding/utf32_encode_byte_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/encoding/utf32_encode_byte_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/encoding/utf32_encode_byte_guard_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps valid little-endian serialization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/utf32_encode_byte_guard_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps valid big-endian serialization' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/encoding/utf32_encode_byte_guard_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'serializes negative scalars as replacement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
