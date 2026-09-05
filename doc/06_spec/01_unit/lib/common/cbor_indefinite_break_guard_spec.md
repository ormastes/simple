# Cbor Indefinite Break Guard Specification

> Tests covering CBOR indefinite string break guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cbor Indefinite Break Guard Specification

## Scenarios

### CBOR indefinite string break guards

#### rejects indefinite byte strings without break

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects indefinite byte strings without break


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects indefinite byte strings without break")
var encoded = [make_initial_byte(major_byte_string(), addl_indefinite())]
val chunk = cbor_encode_bytes([1, 2])
for b in chunk:
    encoded = encoded.push(b)
val result = cbor_decode_bytes(encoded, 0)
assert_equal(result.1, 0)
```

</details>

#### rejects indefinite text strings without break

- rejects indefinite text strings without break


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects indefinite text strings without break")
var encoded = [make_initial_byte(major_text_string(), addl_indefinite())]
val chunk = cbor_encode_text("ok")
for b in chunk:
    encoded = encoded.push(b)
val result = cbor_decode_text(encoded, 0)
assert_equal(result.1, 0)
```

</details>

#### keeps indefinite byte strings with break valid

- keeps indefinite byte strings with break valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps indefinite byte strings with break valid")
var encoded = [make_initial_byte(major_byte_string(), addl_indefinite())]
val chunk = cbor_encode_bytes([1, 2])
for b in chunk:
    encoded = encoded.push(b)
encoded = encoded.push(0xFF)
val result = cbor_decode_bytes(encoded, 0)
assert_equal(result.0.len(), 2)
assert_equal(result.1, encoded.len())
```

</details>

#### keeps indefinite text strings with break valid

- keeps indefinite text strings with break valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps indefinite text strings with break valid")
var encoded = [make_initial_byte(major_text_string(), addl_indefinite())]
val chunk = cbor_encode_text("ok")
for b in chunk:
    encoded = encoded.push(b)
encoded = encoded.push(0xFF)
val result = cbor_decode_text(encoded, 0)
assert_equal(result.0, "ok")
assert_equal(result.1, encoded.len())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/cbor_indefinite_break_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CBOR indefinite string break guards.
- CBOR indefinite string break guards

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

- Canonical SPipe generation for source `6f3873b7dfe190ff35dfc2c3d7bbfaa49f85ce8376d5bbbb69f1e45e8df39ae9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6f3873b7dfe190ff35dfc2c3d7bbfaa49f85ce8376d5bbbb69f1e45e8df39ae9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6f3873b7dfe190ff35dfc2c3d7bbfaa49f85ce8376d5bbbb69f1e45e8df39ae9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/cbor_indefinite_break_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/common/cbor_indefinite_break_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/cbor_indefinite_break_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/cbor_indefinite_break_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/cbor_indefinite_break_guard_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects indefinite byte strings without break' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/cbor_indefinite_break_guard_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects indefinite text strings without break' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/cbor_indefinite_break_guard_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps indefinite byte strings with break valid' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
