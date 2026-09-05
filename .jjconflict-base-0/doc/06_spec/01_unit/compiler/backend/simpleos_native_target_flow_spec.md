# Simpleos Native Target Flow Specification

> Tests covering SimpleOS native target flow.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simpleos Native Target Flow Specification

## Scenarios

### SimpleOS native target flow

#### keeps the logical SimpleOS target through codegen and sysroot linking

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps the logical SimpleOS target through codegen and sysroot linking
   - Expected: backend_helper_native_target_for("simpleos-x86_64") equals `CodegenTarget.SimpleOS_X86_64`
   - Expected: backend_helper_native_target_for("x86_64-unknown-simpleos") equals `CodegenTarget.SimpleOS_X86_64`
   - Expected: LlvmTargetTriple.from_target(CodegenTarget.SimpleOS_X86_64).to_text() equals `x86_64-unknown-simpleos`
   - Expected: toolchain.triple equals `x86_64-unknown-simpleos`
   - Expected: toolchain.sysroot equals `build/os/sysroot`
   - Expected: link_inputs[0] equals `build/os/sysroot/lib/crt0.o`
   - Expected: link_inputs[2] equals `build/os/sysroot/lib/libsimpleos_c.a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the logical SimpleOS target through codegen and sysroot linking")
expect(backend_helper_native_target_for("simpleos-x86_64")).to_equal(CodegenTarget.SimpleOS_X86_64)
expect(is_simpleos_x86_64_target("simpleos-x86_64")).to_be(true)
expect(backend_helper_native_target_for("x86_64-unknown-simpleos")).to_equal(CodegenTarget.SimpleOS_X86_64)
expect(is_simpleos_x86_64_target("x86_64-unknown-simpleos")).to_be(true)
expect(LlvmTargetTriple.from_target(CodegenTarget.SimpleOS_X86_64).to_text()).to_equal("x86_64-unknown-simpleos")
val toolchain = toolchain_for_target(CodegenTarget.SimpleOS_X86_64)
expect(toolchain.triple).to_equal("x86_64-unknown-simpleos")
expect(toolchain.sysroot).to_equal("build/os/sysroot")
val link_inputs = simpleos_x86_64_user_link_inputs("build/os/sysroot")
expect(link_inputs[0]).to_equal("build/os/sysroot/lib/crt0.o")
expect(link_inputs[1]).to_end_with("libsimple_runtime.a")
expect(link_inputs[2]).to_equal("build/os/sysroot/lib/libsimpleos_c.a")
val link_source = compiler_native_link_source()
expect(link_source).to_contain("if target == \"simpleos\" or target == \"simpleos-x86_64\"")
```

</details>

#### routes every canonical multi-architecture SimpleOS selector before hosted linking

- routes every canonical multi-architecture SimpleOS selector before hosted linking


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes every canonical multi-architecture SimpleOS selector before hosted linking")
expect(is_simpleos_x86_64_target("x86_64-unknown-simpleos-elf")).to_be(true)
expect(is_simpleos_arm64_target("aarch64-simpleos")).to_be(true)
expect(is_simpleos_arm64_target("aarch64-unknown-simpleos")).to_be(true)
expect(is_simpleos_riscv64_target("riscv64gc-simpleos")).to_be(true)
expect(is_simpleos_riscv64_target("riscv64gc-unknown-simpleos")).to_be(true)
expect(is_simpleos_riscv64_target("riscv64gc-unknown-none-elf")).to_be(true)
expect(is_simpleos_riscv32_target("riscv32imac-simpleos")).to_be(true)
expect(is_simpleos_riscv32_target("riscv32imac-unknown-simpleos")).to_be(true)
expect(is_simpleos_riscv32_target("riscv32imac-unknown-none-elf")).to_be(true)
```

</details>

#### keeps the RV64 desktop on the explicit hard-float profile

- keeps the RV64 desktop on the explicit hard-float profile


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the RV64 desktop on the explicit hard-float profile")
val targets = read_file_text("src/os/_QemuRunner/scenario_disks.spl") ?? ""
val llvm_target = read_file_text("src/compiler/70.backend/backend/llvm_target.spl") ?? ""
expect(targets).to_contain("target_triple: \"riscv64gc-unknown-none\"")
expect(llvm_target).to_contain("fn llvm_riscv64_hard_float_requested() -> bool")
expect(llvm_target).to_contain("riscv_linux_target_contract_portable_numeric(target)")
```

</details>

#### does not infer SimpleOS from an RV32 filename when a hosted target is explicit

- does not infer SimpleOS from an RV32 filename when a hosted target is explicit


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not infer SimpleOS from an RV32 filename when a hosted target is explicit")
expect(is_simpleos_riscv32_link_for_target("riscv32-unknown-linux-gnu", [], "build/rv32-app")).to_be(false)
expect(is_simpleos_riscv32_link_for_target("riscv32-unknown-none-elf", [], "build/app")).to_be(true)
expect(is_simpleos_riscv32_link_for_target("", [], "build/rv32-app")).to_be(true)
```

</details>

#### keeps the legacy bare-metal x86 target on the SimpleOS kernel lane

- keeps the legacy bare-metal x86 target on the SimpleOS kernel lane
   - Expected: backend_helper_native_target_for("x86_64-unknown-none-elf") equals `CodegenTarget.X86_64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the legacy bare-metal x86 target on the SimpleOS kernel lane")
expect(backend_helper_native_target_for("x86_64-unknown-none-elf")).to_equal(CodegenTarget.X86_64)
expect(is_simpleos_x86_64_target("x86_64-unknown-none-elf")).to_be(true)
```

</details>

#### recognizes x86, ARM, and RISC-V architecture aliases before host fallback

- recognizes x86, ARM, and RISC-V architecture aliases before host fallback
   - Expected: backend_helper_native_target_for("amd64") equals `CodegenTarget.X86_64`
   - Expected: backend_helper_native_target_for("amd64-unknown-linux-gnu") equals `CodegenTarget.X86_64`
   - Expected: backend_helper_native_target_for("x64") equals `CodegenTarget.X86_64`
   - Expected: backend_helper_native_target_for("i386-unknown-linux-gnu") equals `CodegenTarget.X86`
   - Expected: backend_helper_native_target_for("i686-pc-windows-msvc") equals `CodegenTarget.X86`
   - Expected: backend_helper_native_target_for("armv7-unknown-linux-gnueabihf") equals `CodegenTarget.Arm`
   - Expected: backend_helper_native_target_for("thumbv7em-none-eabihf") equals `CodegenTarget.Arm`
   - Expected: backend_helper_native_target_for("aarch64-unknown-linux-gnu") equals `CodegenTarget.AArch64`
   - Expected: backend_helper_native_target_for("arm64-apple-darwin") equals `CodegenTarget.AArch64`
   - Expected: backend_helper_native_target_for("riscv32imac-unknown-none-elf") equals `CodegenTarget.Riscv32`
   - Expected: backend_helper_native_target_for("rv32") equals `CodegenTarget.Riscv32`
   - Expected: backend_helper_native_target_for("riscv64gc-unknown-linux-gnu") equals `CodegenTarget.Riscv64`
   - Expected: backend_helper_native_target_for("rv64") equals `CodegenTarget.Riscv64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recognizes x86, ARM, and RISC-V architecture aliases before host fallback")
expect(backend_helper_native_target_for("amd64")).to_equal(CodegenTarget.X86_64)
expect(backend_helper_native_target_for("amd64-unknown-linux-gnu")).to_equal(CodegenTarget.X86_64)
expect(backend_helper_native_target_for("x64")).to_equal(CodegenTarget.X86_64)
expect(backend_helper_native_target_for("i386-unknown-linux-gnu")).to_equal(CodegenTarget.X86)
expect(backend_helper_native_target_for("i686-pc-windows-msvc")).to_equal(CodegenTarget.X86)
expect(backend_helper_native_target_for("armv7-unknown-linux-gnueabihf")).to_equal(CodegenTarget.Arm)
expect(backend_helper_native_target_for("thumbv7em-none-eabihf")).to_equal(CodegenTarget.Arm)
expect(backend_helper_native_target_for("aarch64-unknown-linux-gnu")).to_equal(CodegenTarget.AArch64)
expect(backend_helper_native_target_for("arm64-apple-darwin")).to_equal(CodegenTarget.AArch64)
expect(backend_helper_native_target_for("riscv32imac-unknown-none-elf")).to_equal(CodegenTarget.Riscv32)
expect(backend_helper_native_target_for("rv32")).to_equal(CodegenTarget.Riscv32)
expect(backend_helper_native_target_for("riscv64gc-unknown-linux-gnu")).to_equal(CodegenTarget.Riscv64)
expect(backend_helper_native_target_for("rv64")).to_equal(CodegenTarget.Riscv64)
```

</details>

#### resolves an explicit SimpleOS target before probing the compiler host

- resolves an explicit SimpleOS target before probing the compiler host
   - Expected: config.triple.to_text() equals `x86_64-unknown-simpleos`
   - Expected: config.triple.datalayout() equals `e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves an explicit SimpleOS target before probing the compiler host")
val source = read_file_text("src/compiler/70.backend/backend/llvm_target.spl") ?? ""
val simpleos_guard = source.index_of("if target == CodegenTarget.SimpleOS_X86_64:")
val simpleos_return = source.index_of("return simpleos_triple")
val hosted_probe = source.index_of("val host_os = get_host_os()")
expect(simpleos_guard).to_be_greater_than(-1)
expect(simpleos_return).to_be_greater_than(simpleos_guard)
expect(hosted_probe).to_be_greater_than(simpleos_return)
expect(hosted_probe).to_be_greater_than(simpleos_guard)

val config = LlvmTargetConfig.for_target_portable_numeric(CodegenTarget.SimpleOS_X86_64, nil)
expect(config.triple.to_text()).to_equal("x86_64-unknown-simpleos")
expect(config.triple.datalayout()).to_equal("e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/backend/simpleos_native_target_flow_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS native target flow.
- SimpleOS native target flow

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `eee17b5dc3b32c6b8484eb83a2da61f9fea60d2f34dae299c583de41bd16f5f6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eee17b5dc3b32c6b8484eb83a2da61f9fea60d2f34dae299c583de41bd16f5f6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eee17b5dc3b32c6b8484eb83a2da61f9fea60d2f34dae299c583de41bd16f5f6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/backend/simpleos_native_target_flow_spec.spl
mirror: doc/06_spec/01_unit/compiler/backend/simpleos_native_target_flow_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/backend/simpleos_native_target_flow_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/backend/simpleos_native_target_flow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/backend/simpleos_native_target_flow_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the logical SimpleOS target through codegen and sysroot linking' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/simpleos_native_target_flow_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes every canonical multi-architecture SimpleOS selector before hosted linking' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/backend/simpleos_native_target_flow_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the RV64 desktop on the explicit hard-float profile' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
