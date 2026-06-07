# Portable Numeric Plan Threading Specification

> Tests that `NativeCodegenAdapter.plan()` exposes the lowering plan derived from `options.target`.

<!-- sdn-diagram:id=portable_numeric_plan_threading_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=portable_numeric_plan_threading_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

portable_numeric_plan_threading_spec -> std
portable_numeric_plan_threading_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=portable_numeric_plan_threading_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Portable Numeric Plan Threading Specification

Tests that `NativeCodegenAdapter.plan()` exposes the lowering plan derived from `options.target`.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PSFM-001 |
| Category | Compiler Backend |
| Difficulty | 3/5 |
| Status | Draft (Phase 2 — awaiting Phase 5 implementation) |
| Requirements | doc/02_requirements/feature/portable_simd_fp_modules.md |
| Plan | doc/03_plan/agent_tasks/portable_simd_fp_modules.md |
| Design | doc/05_design/portable_simd_fp_modules.md |
| Research | N/A |
| Source | `test/01_unit/compiler/portable_numeric_plan_threading_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that `NativeCodegenAdapter.plan()` exposes the lowering plan derived from
`options.target`.

This is the AC-3 native-path wiring: the plan must be threaded into `native_compile_result`
and arch-specific dispatch functions so that capability-aware ISel can gate float and vector
lowering without re-deriving the plan per call.

Run in interpreter mode only (no --mode flag):
  bin/simple test --no-cache test/unit/compiler/portable_numeric_plan_threading_spec.spl

Compile-mode regressions: file a separate FR; do not normalize (AC-6 policy).

## Scenarios

### NativeCodegenAdapter plan field threading

#### x86_64 target

#### AC-3/P2-5a: NativeCodegenAdapter for x86_64 reports runtime-probe SIMD plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange: build CompileOptions targeting x86_64 and wrap in adapter
val opts = CompileOptions(
    target: CodegenTarget.X86_64,
    opt_level: OptimizationLevel.Speed,
    debug_info: false,
    emit_assembly: false,
    emit_llvm_ir: false,
    emit_mir: false,
    verify_output: true
)
val adapter = NativeCodegenAdapter(options: opts)
val plan = adapter.plan()
expect(plan.capabilities.requires_runtime_simd_probe).to_equal(true)
expect(plan.lowering_modules_csv().contains("x86_avx")).to_equal(true)
```

</details>

#### riscv64 target

#### AC-3/P2-5b: NativeCodegenAdapter for riscv64 reports scalar-only default plan

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Arrange: build CompileOptions targeting riscv64 and wrap in adapter
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
val plan = adapter.plan()
expect(plan.capabilities.has_riscv_f).to_equal(true)
expect(plan.capabilities.has_riscv_d).to_equal(true)
expect(plan.capabilities.has_vector_simd).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/portable_simd_fp_modules.md](doc/02_requirements/feature/portable_simd_fp_modules.md)
- **Plan:** [doc/03_plan/agent_tasks/portable_simd_fp_modules.md](doc/03_plan/agent_tasks/portable_simd_fp_modules.md)
- **Design:** [doc/05_design/portable_simd_fp_modules.md](doc/05_design/portable_simd_fp_modules.md)


</details>
