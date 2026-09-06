# Regeneration Theorem Emission Class Specification

> Tests covering Lean regenerator theorem-emission class.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Regeneration Theorem Emission Class Specification

## Scenarios

### Lean regenerator theorem-emission class

#### every generator emits at least one proof obligation

#### async_compile emits a theorem

- async_compile emits a theorem
   - Expected: lean_code contains `theorem `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("async_compile emits a theorem")
val lean_code = regen_async.regenerate_async_compile()
expect(lean_code.contains("theorem ")).to_equal(true)
```

</details>

#### gc_manual_borrow emits a theorem

- gc_manual_borrow emits a theorem
   - Expected: lean_code contains `theorem `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gc_manual_borrow emits a theorem")
val lean_code = regen_gc.regenerate_gc_manual_borrow()
expect(lean_code.contains("theorem ")).to_equal(true)
```

</details>

#### memory_capabilities emits a theorem

- memory_capabilities emits a theorem
   - Expected: lean_code contains `theorem `


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("memory_capabilities emits a theorem")
val lean_code = regen_mem_cap.regenerate_memory_capabilities()
expect(lean_code.contains("theorem ")).to_equal(true)
```

</details>

#### a model without proofs is not verification

#### memory_capabilities emits its model

- memory_capabilities emits its model


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("memory_capabilities emits its model")
val lean_code = regen_mem_cap.regenerate_memory_capabilities()
expect(lean_code).to_contain("inductive RefCapability")
expect(lean_code).to_contain("def canConvert")
```

</details>

#### memory_capabilities model is accompanied by a proof, not just a definition

- memory_capabilities model is accompanied by a proof, not just a definition
   - Expected: has_model and has_proof is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("memory_capabilities model is accompanied by a proof, not just a definition")
val lean_code = regen_mem_cap.regenerate_memory_capabilities()
val has_model = lean_code.contains("def canConvert")
val has_proof = lean_code.contains("theorem ")
expect(has_model and has_proof).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/verification/regeneration_theorem_emission_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Lean regenerator theorem-emission class.
- Lean regenerator theorem-emission class

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

- Canonical SPipe generation for source `b8fa288e572eab364cc15b443405af5ac8002c3ff1cc5e830e5646d19ab0f101`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b8fa288e572eab364cc15b443405af5ac8002c3ff1cc5e830e5646d19ab0f101`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b8fa288e572eab364cc15b443405af5ac8002c3ff1cc5e830e5646d19ab0f101`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/verification/regeneration_theorem_emission_class_spec.spl
mirror: doc/06_spec/unit/compiler/verification/regeneration_theorem_emission_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/verification/regeneration_theorem_emission_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/verification/regeneration_theorem_emission_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/verification/regeneration_theorem_emission_class_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'async_compile emits a theorem' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/verification/regeneration_theorem_emission_class_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gc_manual_borrow emits a theorem' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/verification/regeneration_theorem_emission_class_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'memory_capabilities emits a theorem' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
