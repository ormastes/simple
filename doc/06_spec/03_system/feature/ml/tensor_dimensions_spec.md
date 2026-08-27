# Tensor Dimension Inference Specification

> Verifies the current tensor dimension inference artifact set: the source model defines concrete, named, variable, dynamic, and broadcast dimensions; the Lean regenerator emits the matching verification model; and public docs point at the same feature.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tensor Dimension Inference Specification

Verifies the current tensor dimension inference artifact set: the source model defines concrete, named, variable, dynamic, and broadcast dimensions; the Lean regenerator emits the matching verification model; and public docs point at the same feature.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #193 |
| Category | ML |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | doc/02_requirements/feature/category/Data_Structures.md |
| Plan | N/A |
| Design | doc/05_design/tensor_dimensions_design.md |
| Research | N/A |
| Source | `test/03_system/feature/ml/tensor_dimensions_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the current tensor dimension inference artifact set: the source model
defines concrete, named, variable, dynamic, and broadcast dimensions; the Lean
regenerator emits the matching verification model; and public docs point at the
same feature.

## Scenarios

### Tensor dimension inference traceability

#### documents all dimension variants in the source model

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- documents all dimension variants in the source model


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("documents all dimension variants in the source model")
val source = _read(MODEL_PATH)
expect(source).to_contain("enum Dim:")
expect(source).to_contain("Literal(value: i32)")
expect(source).to_contain("Var(variable: DimVar)")
expect(source).to_contain("Named(name: text, range: Option<(i32, i32)>)")
expect(source).to_contain("Dynamic")
expect(source).to_contain("Broadcast")
```

</details>

#### generates the Lean tensor dimensions verification model

- generates the Lean tensor dimensions verification model


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates the Lean tensor dimensions verification model")
val source = _read(REGEN_PATH)
expect(source).to_contain("fn regenerate_tensor_dimensions() -> text:")
expect(source).to_contain("TensorDimensions")
expect(source).to_contain("def unifyDim : Dim → Dim → UnifyResult")
expect(source).to_contain("def matmulShape (left right : TensorShape) : Option TensorShape :=")
```

</details>

#### keeps guide, design, and Lean proof artifacts linked

- keeps guide, design, and Lean proof artifacts linked


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps guide, design, and Lean proof artifacts linked")
val guide = _read(GUIDE_PATH)
val design = _read(DESIGN_PATH)
val lean = _read(LEAN_PATH)
expect(guide).to_contain("Tensor Dimension")
expect(design).to_contain("Tensor dimension inference")
expect(lean).to_contain("namespace TensorDimensions")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/category/Data_Structures.md`
- **Design:** `doc/05_design/tensor_dimensions_design.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `80a159f17c7ee6c5c4c5b103217d9a576ef6258dbe78a2e199e0a58de6073739`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `80a159f17c7ee6c5c4c5b103217d9a576ef6258dbe78a2e199e0a58de6073739`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `80a159f17c7ee6c5c4c5b103217d9a576ef6258dbe78a2e199e0a58de6073739`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/ml/tensor_dimensions_spec.spl
mirror: doc/06_spec/03_system/feature/ml/tensor_dimensions_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/ml/tensor_dimensions_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/ml/tensor_dimensions_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/ml/tensor_dimensions_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'documents all dimension variants in the source model' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/ml/tensor_dimensions_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates the Lean tensor dimensions verification model' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/ml/tensor_dimensions_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps guide, design, and Lean proof artifacts linked' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
