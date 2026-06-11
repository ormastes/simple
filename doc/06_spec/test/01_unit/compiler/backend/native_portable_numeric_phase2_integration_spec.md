# Native Portable Numeric Phase2 Integration Specification

> <details>

<!-- sdn-diagram:id=native_portable_numeric_phase2_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_portable_numeric_phase2_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_portable_numeric_phase2_integration_spec -> std
native_portable_numeric_phase2_integration_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_portable_numeric_phase2_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Portable Numeric Phase2 Integration Specification

## Scenarios

### Native portable numeric phase-2 integration scaffolding

#### maps native and host targets onto the current x86_64 portable numeric preset

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_preset = portable_numeric_preset_for_target(CodegenTarget.Host)
val native_caps = portable_numeric_capabilities_for_target(CodegenTarget.Native)
val native_plan = portable_numeric_default_plan_for_target(CodegenTarget.Native)

expect(host_preset.name).to_equal("linux-x86_64")
expect(host_preset.arch).to_equal("x86_64")
expect(native_caps.has_scalar_fp).to_equal(true)
expect(native_caps.has_vector_simd).to_equal(true)
expect(native_caps.requires_runtime_simd_probe).to_equal(true)
expect(native_plan.lowering_modules_csv()).to_equal("scalar_fp,vector_simd,scalar_fallback,x86_avx")
expect(native_plan.diagnostics_csv()).to_equal("x86_avx_requires_runtime_probe")
```

</details>

#### keeps RISC-V and scalar-only planning wired through exported helper functions

1. PortableNumericFeatureSelection scalar only
   - Expected: rv64_plan.capabilities.has_riscv_f is true
   - Expected: rv64_plan.capabilities.has_riscv_d is true
   - Expected: rv64_plan.capabilities.has_riscv_v is false
   - Expected: rv64_plan.lowering_modules_csv() equals `scalar_fp,scalar_fallback,riscv_fd`
   - Expected: rv64_plan.diagnostics_csv() equals `vector_simd_requested_but_target_lacks_vector_capability`
   - Expected: rv64_scalar_only.lowering_modules_csv() equals `scalar_fp,scalar_fallback,riscv_fd`
   - Expected: rv64_scalar_only.diagnostics_csv() equals ``
   - Expected: rv32_plan.lowering_modules_csv() equals `scalar_fallback`
   - Expected: rv32_plan.diagnostics_csv() equals `scalar_fp_requested_but_target_lacks_fp,vector_simd_requested_but_target_lack... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rv64_plan = portable_numeric_default_plan_for_target(CodegenTarget.Riscv64)
val rv64_scalar_only = portable_numeric_lowering_plan_for_target(
    CodegenTarget.Riscv64,
    PortableNumericFeatureSelection.scalar_only()
)
val rv32_plan = portable_numeric_default_plan_for_target(CodegenTarget.Riscv32)

expect(rv64_plan.capabilities.has_riscv_f).to_equal(true)
expect(rv64_plan.capabilities.has_riscv_d).to_equal(true)
expect(rv64_plan.capabilities.has_riscv_v).to_equal(false)
expect(rv64_plan.lowering_modules_csv()).to_equal("scalar_fp,scalar_fallback,riscv_fd")
expect(rv64_plan.diagnostics_csv()).to_equal("vector_simd_requested_but_target_lacks_vector_capability")
expect(rv64_scalar_only.lowering_modules_csv()).to_equal("scalar_fp,scalar_fallback,riscv_fd")
expect(rv64_scalar_only.diagnostics_csv()).to_equal("")
expect(rv32_plan.lowering_modules_csv()).to_equal("scalar_fallback")
expect(rv32_plan.diagnostics_csv()).to_equal("scalar_fp_requested_but_target_lacks_fp,vector_simd_requested_but_target_lacks_vector_capability")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/native_portable_numeric_phase2_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Native portable numeric phase-2 integration scaffolding

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
