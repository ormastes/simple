# Portable Numeric Capabilities Specification

> Tests covering Portable numeric capability registry.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Portable Numeric Capabilities Specification

## Scenarios

### Portable numeric capability registry

#### derives x86_64 and RISC-V lowering plans from target presets

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- derives x86_64 and RISC-V lowering plans from target presets
   - Expected: file_write(script_path, portable_numeric_script()) is true
   - Expected: result.exit_code equals `0`
   - Expected: result.stdout contains `x86-ok`
   - Expected: result.stdout contains `rv64-ok`
   - Expected: result.stdout contains `rv64-scalar-only-ok`
   - Expected: result.stdout contains `rv32-ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("derives x86_64 and RISC-V lowering plans from target presets")
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

- maps backend codegen targets to portable numeric plans
   - Expected: host_plan.capabilities.has_scalar_fp is true
   - Expected: host_plan.capabilities.has_vector_simd is true
   - Expected: host_plan.lowering_modules_csv() equals `scalar_fp,vector_simd,scalar_fallback,x86_avx`
   - Expected: rv32_plan.capabilities.has_scalar_fp is false
   - Expected: rv32_plan.capabilities.has_vector_simd is false
   - Expected: rv32_plan.lowering_modules_csv() equals `scalar_fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("maps backend codegen targets to portable numeric plans")
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

- builds a conservative llvm config for x86_64 portable numeric mode
   - Expected: config.cpu equals `x86-64-v1`
   - Expected: config.supports_avx2() is false
   - Expected: config.to_feature_string() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("builds a conservative llvm config for x86_64 portable numeric mode")
val config = LlvmTargetConfig.for_target_portable_numeric(CodegenTarget.X86_64, nil)
expect(config.cpu).to_equal("x86-64-v1")
expect(config.supports_avx2()).to_equal(false)
expect(config.to_feature_string()).to_equal("")
```

</details>

#### builds an integer-only rv32 baremetal contract in portable numeric mode

- builds an integer-only rv32 baremetal contract in portable numeric mode
   - Expected: contract.abi.to_text() equals `ilp32`
   - Expected: contract.march equals `rv32imac`
   - Expected: contract.features does not contain `+f`
   - Expected: contract.features does not contain `+d`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("builds an integer-only rv32 baremetal contract in portable numeric mode")
val contract = riscv_baremetal_target_contract_portable_numeric(CodegenTarget.Riscv32)
expect(contract.abi.to_text()).to_equal("ilp32")
expect(contract.march).to_equal("rv32imac")
expect(contract.features.contains("+f")).to_equal(false)
expect(contract.features.contains("+d")).to_equal(false)
```

</details>

#### AC-1/P2-2: x86_64 generic preset keeps AVX flags out of LLVM features list

- AC-1/P2-2: x86_64 generic preset keeps AVX flags out of LLVM features list
   - Expected: config.cpu equals `x86-64-v1`
   - Expected: config.features does not contain `+avx`
   - Expected: config.features does not contain `+avx2`
   - Expected: config.to_feature_string() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AC-1/P2-2: x86_64 generic preset keeps AVX flags out of LLVM features list")
val config = LlvmTargetConfig.for_target_portable_numeric(CodegenTarget.X86_64, nil)
expect(config.cpu).to_equal("x86-64-v1")
expect(config.features.contains("+avx")).to_equal(false)
expect(config.features.contains("+avx2")).to_equal(false)
expect(config.to_feature_string()).to_equal("")
```

</details>

#### AC-2/P2-3: rv64_linux portable plan has has_riscv_f and has_riscv_d from registry

- AC-2/P2-3: rv64_linux portable plan has has_riscv_f and has_riscv_d from registry
   - Expected: plan.capabilities.has_riscv_f is true
   - Expected: plan.capabilities.has_riscv_d is true
   - Expected: plan.capabilities.has_riscv_v is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AC-2/P2-3: rv64_linux portable plan has has_riscv_f and has_riscv_d from registry")
val plan = portable_numeric_default_plan_for_target(CodegenTarget.Riscv64)
expect(plan.capabilities.has_riscv_f).to_equal(true)
expect(plan.capabilities.has_riscv_d).to_equal(true)
expect(plan.capabilities.has_riscv_v).to_equal(false)
```

</details>

#### AC-2/P2-4: rv32_baremetal int-only preset has no FP or vector capability flags

- AC-2/P2-4: rv32_baremetal int-only preset has no FP or vector capability flags
   - Expected: plan.capabilities.has_riscv_f is false
   - Expected: plan.capabilities.has_riscv_d is false
   - Expected: plan.capabilities.has_riscv_v is false
   - Expected: plan.capabilities.has_scalar_fp is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AC-2/P2-4: rv32_baremetal int-only preset has no FP or vector capability flags")
val plan = portable_numeric_default_plan_for_target(CodegenTarget.Riscv32)
expect(plan.capabilities.has_riscv_f).to_equal(false)
expect(plan.capabilities.has_riscv_d).to_equal(false)
expect(plan.capabilities.has_riscv_v).to_equal(false)
expect(plan.capabilities.has_scalar_fp).to_equal(false)
```

</details>

#### AC-4/GAP-1: generic x86_64 LLVM target does not claim AVX or AVX2 features

- AC-4/GAP-1: generic x86_64 LLVM target does not claim AVX or AVX2 features
   - Expected: config.cpu equals `x86-64-v1`
   - Expected: config.features does not contain `+avx`
   - Expected: config.features does not contain `+avx2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("AC-4/GAP-1: generic x86_64 LLVM target does not claim AVX or AVX2 features")
val config = LlvmTargetConfig.for_target_portable_numeric(CodegenTarget.X86_64, nil)
expect(config.cpu).to_equal("x86-64-v1")
expect(config.features.contains("+avx")).to_equal(false)
expect(config.features.contains("+avx2")).to_equal(false)
```

</details>

#### Feature-B-contract: Zicbom/Zicboz/Zicbop/cache-probe fields are false across all presets

- Feature-B-contract: Zicbom/Zicboz/Zicbop/cache-probe fields are false across all presets
   - Expected: x86_plan.capabilities.has_riscv_zicbom is false
   - Expected: x86_plan.capabilities.has_riscv_zicboz is false
   - Expected: x86_plan.capabilities.has_riscv_zicbop is false
   - Expected: x86_plan.capabilities.requires_runtime_cache_probe is false
   - Expected: rv64_plan.capabilities.has_riscv_zicbom is false
   - Expected: rv64_plan.capabilities.has_riscv_zicboz is false
   - Expected: rv64_plan.capabilities.has_riscv_zicbop is false
   - Expected: rv64_plan.capabilities.requires_runtime_cache_probe is false
   - Expected: rv32_plan.capabilities.has_riscv_zicbom is false
   - Expected: rv32_plan.capabilities.has_riscv_zicboz is false
   - Expected: rv32_plan.capabilities.has_riscv_zicbop is false
   - Expected: rv32_plan.capabilities.requires_runtime_cache_probe is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("Feature-B-contract: Zicbom/Zicboz/Zicbop/cache-probe fields are false across all presets")
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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Portable numeric capability registry.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `19b0ea2e2bb9a46ceb584576c1a5f3325c7f1dc71f7f42ad0a090243b04806a6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `19b0ea2e2bb9a46ceb584576c1a5f3325c7f1dc71f7f42ad0a090243b04806a6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `19b0ea2e2bb9a46ceb584576c1a5f3325c7f1dc71f7f42ad0a090243b04806a6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/portable_numeric_capabilities_spec.spl
mirror: doc/06_spec/01_unit/compiler/portable_numeric_capabilities_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/portable_numeric_capabilities_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/portable_numeric_capabilities_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/portable_numeric_capabilities_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/portable_numeric_capabilities_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives x86_64 and RISC-V lowering plans from target presets' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/portable_numeric_capabilities_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps backend codegen targets to portable numeric plans' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/portable_numeric_capabilities_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a conservative llvm config for x86_64 portable numeric mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
