# U64 Hex Literal Precision Specification

> Tests covering u64 hex literal precision.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# U64 Hex Literal Precision Specification

## Scenarios

### u64 hex literal precision

#### preserves bit 63 (top bit only)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves bit 63 (top bit only)
   - Expected: v equals `9223372036854775808u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves bit 63 (top bit only)")
var v: u64 = top_bit()
expect(v).to_equal(9223372036854775808u64)
```

</details>

#### preserves all-ones (max u64)

- preserves all-ones (max u64)
   - Expected: v equals `18446744073709551615u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves all-ones (max u64)")
var v: u64 = all_ones()
expect(v).to_equal(18446744073709551615u64)
```

</details>

#### preserves arbitrary 64-bit pattern

- preserves arbitrary 64-bit pattern
   - Expected: v equals `14627333968688430831u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves arbitrary 64-bit pattern")
var v: u64 = cafe_babe()
expect(v).to_equal(14627333968688430831u64)
```

</details>

#### preserves SHA-512 IV constant

- preserves SHA-512 IV constant
   - Expected: v equals `7640891576956012808u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves SHA-512 IV constant")
var v: u64 = sha512_iv()
expect(v).to_equal(7640891576956012808u64)
```

</details>

#### preserves SHA-384 IV5 constant (bit 63 set)

- preserves SHA-384 IV5 constant (bit 63 set)
   - Expected: v equals `15784041429090275239u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves SHA-384 IV5 constant (bit 63 set)")
var v: u64 = sha384_iv5()
expect(v).to_equal(15784041429090275239u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/u64_hex_literal_precision_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering u64 hex literal precision.
- u64 hex literal precision

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `8cdc781a1e20ff7e2530bc269b29bb7ae3c3e477a7948fb14a1c8d38cb21b6ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8cdc781a1e20ff7e2530bc269b29bb7ae3c3e477a7948fb14a1c8d38cb21b6ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8cdc781a1e20ff7e2530bc269b29bb7ae3c3e477a7948fb14a1c8d38cb21b6ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/u64_hex_literal_precision_spec.spl
mirror: doc/06_spec/unit/compiler/u64_hex_literal_precision_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/u64_hex_literal_precision_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/u64_hex_literal_precision_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/u64_hex_literal_precision_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves bit 63 (top bit only)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/u64_hex_literal_precision_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves all-ones (max u64)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/u64_hex_literal_precision_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves arbitrary 64-bit pattern' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
