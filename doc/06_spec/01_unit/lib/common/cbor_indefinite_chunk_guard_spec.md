# Cbor Indefinite Chunk Guard Specification

> Tests covering CBOR indefinite string chunk guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cbor Indefinite Chunk Guard Specification

## Scenarios

### CBOR indefinite string chunk guards

#### rejects nested indefinite byte string chunks

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects nested indefinite byte string chunks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects nested indefinite byte string chunks")
val outer = make_initial_byte(major_byte_string(), addl_indefinite())
val nested = make_initial_byte(major_byte_string(), addl_indefinite())
val encoded = [outer, nested, 0xFF, 0xFF]
val result = cbor_decode_bytes(encoded, 0)
assert_equal(result.1, 0)
```

</details>

#### rejects nested indefinite text string chunks

- rejects nested indefinite text string chunks


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects nested indefinite text string chunks")
val outer = make_initial_byte(major_text_string(), addl_indefinite())
val nested = make_initial_byte(major_text_string(), addl_indefinite())
val encoded = [outer, nested, 0xFF, 0xFF]
val result = cbor_decode_text(encoded, 0)
assert_equal(result.1, 0)
```

</details>

#### keeps definite byte chunks valid

- keeps definite byte chunks valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps definite byte chunks valid")
var encoded = [make_initial_byte(major_byte_string(), addl_indefinite())]
val chunk = cbor_encode_bytes([1])
for b in chunk:
    encoded = encoded.push(b)
encoded = encoded.push(0xFF)
val result = cbor_decode_bytes(encoded, 0)
assert_equal(result.0.len(), 1)
assert_equal(result.1, encoded.len())
```

</details>

#### keeps definite text chunks valid

- keeps definite text chunks valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps definite text chunks valid")
var encoded = [make_initial_byte(major_text_string(), addl_indefinite())]
val chunk = cbor_encode_text("x")
for b in chunk:
    encoded = encoded.push(b)
encoded = encoded.push(0xFF)
val result = cbor_decode_text(encoded, 0)
assert_equal(result.0, "x")
assert_equal(result.1, encoded.len())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/cbor_indefinite_chunk_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CBOR indefinite string chunk guards.
- CBOR indefinite string chunk guards

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

- Canonical SPipe generation for source `e9d20a1c3175563f30cc40580fa1f7deafb49a967c0f5a1ed9b940ec32db9686`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e9d20a1c3175563f30cc40580fa1f7deafb49a967c0f5a1ed9b940ec32db9686`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e9d20a1c3175563f30cc40580fa1f7deafb49a967c0f5a1ed9b940ec32db9686`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/cbor_indefinite_chunk_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/cbor_indefinite_chunk_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/cbor_indefinite_chunk_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/cbor_indefinite_chunk_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/cbor_indefinite_chunk_guard_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects nested indefinite byte string chunks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/cbor_indefinite_chunk_guard_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects nested indefinite text string chunks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/cbor_indefinite_chunk_guard_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps definite byte chunks valid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
