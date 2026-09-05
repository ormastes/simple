# Array F64 Element Precision Specification

> Tests covering f64 container element precision.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Array F64 Element Precision Specification

## Scenarios

### f64 container element precision

#### reads a fractional f64 array element back without precision loss

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads a fractional f64 array element back without precision loss
   - Expected: x == 0.1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads a fractional f64 array element back without precision loss")
val a = [0.1, 0.2, 0.3]
val x = a[0]
expect(x == 0.1).to_equal(true)
```

</details>

#### types an inline user-function f64 return before comparison

- types an inline user-function f64 return before comparison
   - Expected: first_fraction(values) == 0.1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("types an inline user-function f64 return before comparison")
val values = [0.1, 0.2, 0.3]
expect(first_fraction(values) == 0.1).to_equal(true)
```

</details>

#### reads a fractional f64 dict value back without precision loss

- reads a fractional f64 dict value back without precision loss
   - Expected: x == 0.1 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads a fractional f64 dict value back without precision loss")
val d = {"k": 0.1}
val x = d["k"]
expect(x == 0.1).to_equal(true)
```

</details>

#### keeps boxed 0.0 falsy and equal to scalar 0.0

- keeps boxed 0.0 falsy and equal to scalar 0.0
   - Expected: x == 0.0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps boxed 0.0 falsy and equal to scalar 0.0")
val a = [0.0]
val x = a[0]
expect(x == 0.0).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/array_f64_element_precision_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering f64 container element precision.
- f64 container element precision

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

- Canonical SPipe generation for source `067d9a02d7e5760cb4e53636d7c1a8f8469a26f67e447da1836195e07d074d4b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `067d9a02d7e5760cb4e53636d7c1a8f8469a26f67e447da1836195e07d074d4b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `067d9a02d7e5760cb4e53636d7c1a8f8469a26f67e447da1836195e07d074d4b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/array_f64_element_precision_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/array_f64_element_precision_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/array_f64_element_precision_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/array_f64_element_precision_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/array_f64_element_precision_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a fractional f64 array element back without precision loss' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/array_f64_element_precision_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'types an inline user-function f64 return before comparison' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/array_f64_element_precision_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads a fractional f64 dict value back without precision loss' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
