# Bson Specification

> Tests covering BSON encoder — reference vectors, BSON decoder — reference vectors, BSON decoder — error cases, BSON round-trip.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bson Specification

## Scenarios

### BSON encoder — reference vectors

#### empty document

#### encodes empty doc correctly

- encodes empty doc correctly
   - Expected: _check_empty_doc_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes empty doc correctly")
expect(_check_empty_doc_ok()).to_equal(true)
```

</details>

#### Int32

#### encodes int32 field correctly

- encodes int32 field correctly
   - Expected: _check_int32_a1_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes int32 field correctly")
expect(_check_int32_a1_ok()).to_equal(true)
```

</details>

#### String

#### encodes string field correctly

- encodes string field correctly
   - Expected: _check_str_ab_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes string field correctly")
expect(_check_str_ab_ok()).to_equal(true)
```

</details>

#### Null

#### encodes null field correctly

- encodes null field correctly
   - Expected: _check_null_a_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes null field correctly")
expect(_check_null_a_ok()).to_equal(true)
```

</details>

#### Bool

#### encodes bool true field correctly

- encodes bool true field correctly
   - Expected: _check_bool_true_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes bool true field correctly")
expect(_check_bool_true_ok()).to_equal(true)
```

</details>

#### encodes bool false field correctly

- encodes bool false field correctly
   - Expected: _check_bool_false_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes bool false field correctly")
expect(_check_bool_false_ok()).to_equal(true)
```

</details>

#### encode error

#### returns NotADocument when top-level value is not Doc

- returns NotADocument when top-level value is not Doc
   - Expected: _check_not_doc_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns NotADocument when top-level value is not Doc")
expect(_check_not_doc_err()).to_equal(true)
```

</details>

### BSON decoder — reference vectors

#### empty document

#### decodes empty doc bytes correctly

- decodes empty doc bytes correctly
   - Expected: _check_dec_empty_doc() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes empty doc bytes correctly")
expect(_check_dec_empty_doc()).to_equal(true)
```

</details>

#### Int32

#### decodes int32 field bytes correctly

- decodes int32 field bytes correctly
   - Expected: _check_dec_int32_a1() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes int32 field bytes correctly")
expect(_check_dec_int32_a1()).to_equal(true)
```

</details>

#### String

#### decodes string field bytes correctly

- decodes string field bytes correctly
   - Expected: _check_dec_str_ab() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes string field bytes correctly")
expect(_check_dec_str_ab()).to_equal(true)
```

</details>

#### Null

#### decodes null field bytes correctly

- decodes null field bytes correctly
   - Expected: _check_dec_null_a() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes null field bytes correctly")
expect(_check_dec_null_a()).to_equal(true)
```

</details>

#### Bool

#### decodes bool true bytes correctly

- decodes bool true bytes correctly
   - Expected: _check_dec_bool_true() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes bool true bytes correctly")
expect(_check_dec_bool_true()).to_equal(true)
```

</details>

#### decodes bool false bytes correctly

- decodes bool false bytes correctly
   - Expected: _check_dec_bool_false() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decodes bool false bytes correctly")
expect(_check_dec_bool_false()).to_equal(true)
```

</details>

### BSON decoder — error cases

#### too short

#### returns UnexpectedEnd when buffer is under 5 bytes

- returns UnexpectedEnd when buffer is under 5 bytes
   - Expected: _check_dec_too_short() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns UnexpectedEnd when buffer is under 5 bytes")
expect(_check_dec_too_short()).to_equal(true)
```

</details>

#### length mismatch

#### returns LengthMismatch when declared length differs from buffer

- returns LengthMismatch when declared length differs from buffer
   - Expected: _check_dec_length_mismatch() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns LengthMismatch when declared length differs from buffer")
expect(_check_dec_length_mismatch()).to_equal(true)
```

</details>

#### declared length below minimum

#### returns UnexpectedEnd when declared length is under 5

- returns UnexpectedEnd when declared length is under 5
   - Expected: _check_dec_length_too_small() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns UnexpectedEnd when declared length is under 5")
expect(_check_dec_length_too_small()).to_equal(true)
```

</details>

### BSON round-trip

#### empty document round-trips

- empty document round-trips
   - Expected: _rt_empty() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("empty document round-trips")
expect(_rt_empty()).to_equal(true)
```

</details>

#### Int32 round-trips

- Int32 round-trips
   - Expected: _rt_int32() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Int32 round-trips")
expect(_rt_int32()).to_equal(true)
```

</details>

#### Int64 round-trips

- Int64 round-trips
   - Expected: _rt_int64() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Int64 round-trips")
expect(_rt_int64()).to_equal(true)
```

</details>

#### String round-trips

- String round-trips
   - Expected: _rt_string() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("String round-trips")
expect(_rt_string()).to_equal(true)
```

</details>

#### Null round-trips

- Null round-trips
   - Expected: _rt_null() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Null round-trips")
expect(_rt_null()).to_equal(true)
```

</details>

#### Bool true round-trips

- Bool true round-trips
   - Expected: _rt_bool_true() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Bool true round-trips")
expect(_rt_bool_true()).to_equal(true)
```

</details>

#### Bool false round-trips

- Bool false round-trips
   - Expected: _rt_bool_false() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Bool false round-trips")
expect(_rt_bool_false()).to_equal(true)
```

</details>

#### nested document round-trips

- nested document round-trips
   - Expected: _rt_nested() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested document round-trips")
expect(_rt_nested()).to_equal(true)
```

</details>

#### array round-trips

- array round-trips
   - Expected: _rt_array() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array round-trips")
expect(_rt_array()).to_equal(true)
```

</details>

#### binary round-trips

- binary round-trips
   - Expected: _rt_binary() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("binary round-trips")
expect(_rt_binary()).to_equal(true)
```

</details>

#### datetime round-trips

- datetime round-trips
   - Expected: _rt_datetime() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("datetime round-trips")
expect(_rt_datetime()).to_equal(true)
```

</details>

#### regex round-trips

- regex round-trips
   - Expected: _rt_regex() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("regex round-trips")
expect(_rt_regex()).to_equal(true)
```

</details>

#### multi-field document round-trips

- multi-field document round-trips
   - Expected: _rt_multi_field() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multi-field document round-trips")
expect(_rt_multi_field()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/encoding/bson_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BSON encoder — reference vectors, BSON decoder — reference vectors, BSON decoder — error cases, BSON round-trip.
- BSON encoder — reference vectors
- BSON decoder — reference vectors
- BSON decoder — error cases
- BSON round-trip

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
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

- Canonical SPipe generation for source `b093ebd9df0e8b962955571fcb4c704c957aab8cedc2238e1ec111db3e844897`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b093ebd9df0e8b962955571fcb4c704c957aab8cedc2238e1ec111db3e844897`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b093ebd9df0e8b962955571fcb4c704c957aab8cedc2238e1ec111db3e844897`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/encoding/bson_spec.spl
mirror: doc/06_spec/unit/lib/common/encoding/bson_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/encoding/bson_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/encoding/bson_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/encoding/bson_spec.spl:677:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes empty doc correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/encoding/bson_spec.spl:683:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes int32 field correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/encoding/bson_spec.spl:689:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'encodes string field correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
