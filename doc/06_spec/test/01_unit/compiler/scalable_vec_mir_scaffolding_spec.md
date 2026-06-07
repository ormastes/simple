# Scalable Vector MIR Scaffolding Specification

> Tests that: 1. `ScalableVec(element, min_lanes)` is a valid `MirTypeKind` variant (Phase 2 scenario #1) 2. Native adapter guardrails report scalable-vector lowering status explicitly before RV64 ISel can panic.

<!-- sdn-diagram:id=scalable_vec_mir_scaffolding_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=scalable_vec_mir_scaffolding_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

scalable_vec_mir_scaffolding_spec -> std
scalable_vec_mir_scaffolding_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=scalable_vec_mir_scaffolding_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val elem = MirType.i64()
val sv = MirType(kind: MirTypeKind.ScalableVec(element: elem, min_lanes: 4))
expect(sv.kind).to_equal(MirTypeKind.ScalableVec(element: elem, min_lanes: 4))
```

</details>

### NativeCodegenAdapter scalable diagnostics

#### reports lack-of-capability for default riscv64 target when MIR uses ScalableVec

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- **Requirements:** [doc/02_requirements/feature/simd_fixed_and_scalable_vectors.md](doc/02_requirements/feature/simd_fixed_and_scalable_vectors.md)
- **Plan:** [doc/03_plan/agent_tasks/simd_fixed_and_scalable_vectors.md](doc/03_plan/agent_tasks/simd_fixed_and_scalable_vectors.md)
- **Design:** [doc/05_design/simd_fixed_and_scalable_vectors.md](doc/05_design/simd_fixed_and_scalable_vectors.md)


</details>
