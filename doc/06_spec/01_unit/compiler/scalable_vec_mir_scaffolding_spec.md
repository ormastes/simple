# Scalable Vector MIR Scaffolding Specification

> Tests that: 1. `ScalableVec(element, min_lanes)` is a valid `MirTypeKind` variant (Phase 2 scenario #1) 2. Native adapter guardrails report scalable-vector lowering status explicitly before RV64 ISel can panic.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scalable Vector MIR Scaffolding Specification

Tests that: 1. `ScalableVec(element, min_lanes)` is a valid `MirTypeKind` variant (Phase 2 scenario #1) 2. Native adapter guardrails report scalable-vector lowering status explicitly before RV64 ISel can panic.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PSFM-001 |
| Category | Compiler Backend |
| Difficulty | 3/5 |
| Status | Active |
| Requirements | doc/02_requirements/feature/simd_fixed_and_scalable_vectors.md |
| Plan | doc/03_plan/agent_tasks/simd_fixed_and_scalable_vectors.md |
| Design | doc/05_design/simd_fixed_and_scalable_vectors.md |
| Source | `test/01_unit/compiler/scalable_vec_mir_scaffolding_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that:
1. `ScalableVec(element, min_lanes)` is a valid `MirTypeKind` variant (Phase 2 scenario #1)
2. Native adapter guardrails report scalable-vector lowering status explicitly
   before RV64 ISel can panic.

Run in interpreter mode only (no --mode flag):
  bin/simple test --no-cache test/unit/compiler/scalable_vec_mir_scaffolding_spec.spl

Compile-mode regressions: file a separate FR; do not normalize (AC-6 policy).

## Scenarios

### ScalableVec MIR type scaffolding

#### MirTypeKind.ScalableVec variant

#### AC-5/P2-1: ScalableVec MirType can be constructed and pattern-matched

- AC-5/P2-1: ScalableVec MirType can be constructed and pattern-matched
   - Expected: sv.kind equals `MirTypeKind.ScalableVec(element: elem, min_lanes: 4)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AC-5/P2-1: ScalableVec MirType can be constructed and pattern-matched")
val elem = MirType.i64()
val sv = MirType(kind: MirTypeKind.ScalableVec(element: elem, min_lanes: 4))
expect(sv.kind).to_equal(MirTypeKind.ScalableVec(element: elem, min_lanes: 4))
```

</details>

### NativeCodegenAdapter scalable diagnostics

#### reports lack-of-capability for default riscv64 target when MIR uses ScalableVec

- reports lack-of-capability for default riscv64 target when MIR uses ScalableVec
   - Expected: diagnostics.len() equals `1`
   - Expected: diagnostics[0] equals `scalable_vector_target_lacks_native_capability`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports lack-of-capability for default riscv64 target when MIR uses ScalableVec")
val opts = CompileOptions(
    target: CodegenTarget.Riscv64,
    opt_level: OptimizationLevel.Speed,
    debug_info: false,
    emit_assembly: false,
    emit_llvm_ir: false,
    emit_mir: false,
    verify_output: true
)
val adapter = NativeCodegenAdapter(options: opts)
val diagnostics = adapter.scalable_lowering_diagnostics(make_scalable_mir_module())
expect(diagnostics.len()).to_equal(1)
expect(diagnostics[0]).to_equal("scalable_vector_target_lacks_native_capability")
```

</details>

#### reports no scalable diagnostic when MIR module does not use ScalableVec

- reports no scalable diagnostic when MIR module does not use ScalableVec
   - Expected: diagnostics.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reports no scalable diagnostic when MIR module does not use ScalableVec")
val opts = CompileOptions(
    target: CodegenTarget.Riscv64,
    opt_level: OptimizationLevel.Speed,
    debug_info: false,
    emit_assembly: false,
    emit_llvm_ir: false,
    emit_mir: false,
    verify_output: true
)
val adapter = NativeCodegenAdapter(options: opts)
val empty_module = MirModule(name: "empty", functions: {}, statics: {}, constants: {}, types: {})
val diagnostics = adapter.scalable_lowering_diagnostics(empty_module)
expect(diagnostics.len()).to_equal(0)
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

- **Requirements:** `doc/02_requirements/feature/simd_fixed_and_scalable_vectors.md`
- **Plan:** `doc/03_plan/agent_tasks/simd_fixed_and_scalable_vectors.md`
- **Design:** `doc/05_design/simd_fixed_and_scalable_vectors.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ee5dbd00db023fbb57123ced7647d3b380a2c570e0e2188e663108b8ab4b55f4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee5dbd00db023fbb57123ced7647d3b380a2c570e0e2188e663108b8ab4b55f4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee5dbd00db023fbb57123ced7647d3b380a2c570e0e2188e663108b8ab4b55f4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/scalable_vec_mir_scaffolding_spec.spl
mirror: doc/06_spec/01_unit/compiler/scalable_vec_mir_scaffolding_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/scalable_vec_mir_scaffolding_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/scalable_vec_mir_scaffolding_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/scalable_vec_mir_scaffolding_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/scalable_vec_mir_scaffolding_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-5/P2-1: ScalableVec MirType can be constructed and pattern-matched' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/scalable_vec_mir_scaffolding_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports lack-of-capability for default riscv64 target when MIR uses ScalableVec' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/scalable_vec_mir_scaffolding_spec.spl:139:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports no scalable diagnostic when MIR module does not use ScalableVec' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
