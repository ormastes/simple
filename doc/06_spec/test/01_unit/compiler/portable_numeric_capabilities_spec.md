# Portable Numeric Capabilities Specification

> 1. dir create all

<!-- sdn-diagram:id=portable_numeric_capabilities_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=portable_numeric_capabilities_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

portable_numeric_capabilities_spec -> std
portable_numeric_capabilities_spec -> app
portable_numeric_capabilities_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=portable_numeric_capabilities_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Portable Numeric Capabilities Specification

## Scenarios

### Portable numeric capability registry

#### derives x86_64 and RISC-V lowering plans from target presets

1. dir create all
   - Expected: file_write(script_path, portable_numeric_script()) is true
   - Expected: result.exit_code equals `0`
   - Expected: result.stdout contains `x86-ok`
   - Expected: result.stdout contains `rv64-ok`
   - Expected: result.stdout contains `rv64-scalar-only-ok`
   - Expected: result.stdout contains `rv32-ok`
2. shell


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = portable_numeric_fixture_root()
val script_path = portable_numeric_script_path(root)
val simple_bin = "/home/ormastes/dev/pub/simple/bin/simple"
val simple_src = "/home/ormastes/dev/pub/simple/src"

dir_create_all(root)
expect(file_write(script_path, portable_numeric_script())).to_equal(true)

val result = shell("cd {root} && SIMPLE_LIB={simple_src} {simple_bin} run {script_path}")
expect(result.exit_code).to_equal(0)

expect(result.stdout.contains("x86-ok")).to_equal(true)
expect(result.stdout.contains("rv64-ok")).to_equal(true)
expect(result.stdout.contains("rv64-scalar-only-ok")).to_equal(true)
expect(result.stdout.contains("rv32-ok")).to_equal(true)

shell("rm -rf {root}")
```

</details>

#### maps backend codegen targets to portable numeric plans

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val host_plan = portable_numeric_default_plan_for_target(CodegenTarget.Host)
expect(host_plan.capabilities.has_scalar_fp).to_equal(true)
expect(host_plan.capabilities.has_vector_simd).to_equal(true)
expect(host_plan.lowering_modules_csv()).to_equal("scalar_fp,vector_simd,scalar_fallback,x86_avx")

val rv32_plan = portable_numeric_default_plan_for_target(CodegenTarget.Riscv32)
expect(rv32_plan.capabilities.has_scalar_fp).to_equal(false)
expect(rv32_plan.capabilities.has_vector_simd).to_equal(false)
expect(rv32_plan.lowering_modules_csv()).to_equal("scalar_fallback")
```

</details>

#### builds a conservative llvm config for x86_64 portable numeric mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LlvmTargetConfig.for_target_portable_numeric(CodegenTarget.X86_64, nil)
expect(config.cpu).to_equal("x86-64-v1")
expect(config.supports_avx2()).to_equal(false)
expect(config.to_feature_string()).to_equal("")
```

</details>

#### builds an integer-only rv32 baremetal contract in portable numeric mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = riscv_baremetal_target_contract_portable_numeric(CodegenTarget.Riscv32)
expect(contract.abi.to_text()).to_equal("ilp32")
expect(contract.march).to_equal("rv32imac")
expect(contract.features.contains("+f")).to_equal(false)
expect(contract.features.contains("+d")).to_equal(false)
```

</details>

#### AC-1/P2-2: x86_64 generic preset keeps AVX flags out of LLVM features list

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LlvmTargetConfig.for_target_portable_numeric(CodegenTarget.X86_64, nil)
expect(config.cpu).to_equal("x86-64-v1")
expect(config.features.contains("+avx")).to_equal(false)
expect(config.features.contains("+avx2")).to_equal(false)
expect(config.to_feature_string()).to_equal("")
```

</details>

#### AC-2/P2-3: rv64_linux portable plan has has_riscv_f and has_riscv_d from registry

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = portable_numeric_default_plan_for_target(CodegenTarget.Riscv64)
expect(plan.capabilities.has_riscv_f).to_equal(true)
expect(plan.capabilities.has_riscv_d).to_equal(true)
expect(plan.capabilities.has_riscv_v).to_equal(false)
```

</details>

#### AC-2/P2-4: rv32_baremetal int-only preset has no FP or vector capability flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val plan = portable_numeric_default_plan_for_target(CodegenTarget.Riscv32)
expect(plan.capabilities.has_riscv_f).to_equal(false)
expect(plan.capabilities.has_riscv_d).to_equal(false)
expect(plan.capabilities.has_riscv_v).to_equal(false)
expect(plan.capabilities.has_scalar_fp).to_equal(false)
```

</details>

#### AC-4/GAP-1: generic x86_64 LLVM target does not claim AVX or AVX2 features

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = LlvmTargetConfig.for_target_portable_numeric(CodegenTarget.X86_64, nil)
expect(config.cpu).to_equal("x86-64-v1")
expect(config.features.contains("+avx")).to_equal(false)
expect(config.features.contains("+avx2")).to_equal(false)
```

</details>

#### Feature-B-contract: Zicbom/Zicboz/Zicbop/cache-probe fields are false across all presets

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x86_plan = portable_numeric_default_plan_for_target(CodegenTarget.X86_64)
expect(x86_plan.capabilities.has_riscv_zicbom).to_equal(false)
expect(x86_plan.capabilities.has_riscv_zicboz).to_equal(false)
expect(x86_plan.capabilities.has_riscv_zicbop).to_equal(false)
expect(x86_plan.capabilities.requires_runtime_cache_probe).to_equal(false)

val rv64_plan = portable_numeric_default_plan_for_target(CodegenTarget.Riscv64)
expect(rv64_plan.capabilities.has_riscv_zicbom).to_equal(false)
expect(rv64_plan.capabilities.has_riscv_zicboz).to_equal(false)
expect(rv64_plan.capabilities.has_riscv_zicbop).to_equal(false)
expect(rv64_plan.capabilities.requires_runtime_cache_probe).to_equal(false)

val rv32_plan = portable_numeric_default_plan_for_target(CodegenTarget.Riscv32)
expect(rv32_plan.capabilities.has_riscv_zicbom).to_equal(false)
expect(rv32_plan.capabilities.has_riscv_zicboz).to_equal(false)
expect(rv32_plan.capabilities.has_riscv_zicbop).to_equal(false)
expect(rv32_plan.capabilities.requires_runtime_cache_probe).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/portable_numeric_capabilities_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Portable numeric capability registry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
