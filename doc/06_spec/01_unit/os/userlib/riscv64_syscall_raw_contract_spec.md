# Riscv64 Syscall Raw Contract Specification

> Tests covering RISC-V64 raw syscall ABI contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv64 Syscall Raw Contract Specification

## Scenarios

### RISC-V64 raw syscall ABI contract

#### routes through the architecture runtime ecall shim

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- routes through the architecture runtime ecall shim


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes through the architecture runtime ecall shim")
val source = file_read("src/os/userlib/syscall_raw.spl")
expect(source).to_contain("extern fn rt_riscv64_syscall")
expect(source).to_contain("rt_riscv64_syscall(id, arg0, arg1, arg2, arg3, arg4)")

val runtime = file_read("src/os/kernel/arch/riscv64/boot/freestanding_runtime.c")
expect(runtime).to_contain("register spl_u64 a7 __asm__(\"a7\") = id")
expect(runtime).to_contain("__asm__ volatile(\"ecall\"")
expect(runtime).to_contain(": \"+r\"(a0)")

val linker = compiler_native_link_source()
expect(linker).to_contain("int64_t rt_riscv64_syscall")
```

</details>

#### routes CSR operands through immediate architecture runtime cases

- routes CSR operands through immediate architecture runtime cases
   - Expected: cpu does not contain `Identifier("out")`
   - Expected: cpu does not contain `in(reg)`
   - Expected: cpu does not contain `out(reg)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes CSR operands through immediate architecture runtime cases")
val cpu = file_read("src/os/kernel/arch/riscv64/cpu.spl")
expect(cpu).to_contain("extern fn rt_riscv64_csr_read")
expect(cpu).to_contain("rt_riscv64_csr_read(0x100u32)")
expect(cpu.contains("Identifier(\"out\")")).to_equal(false)
expect(cpu.contains("in(reg)")).to_equal(false)
expect(cpu.contains("out(reg)")).to_equal(false)

val runtime = file_read("src/os/kernel/arch/riscv64/boot/freestanding_runtime.c")
expect(runtime).to_contain("RV64_CSR_READ_CASE(0x100U, sstatus)")
expect(runtime).to_contain("csrw satp, %0")
```

</details>

#### routes SBI register operands through the architecture runtime

- routes SBI register operands through the architecture runtime
   - Expected: sbi does not contain `Identifier("arg0")`
   - Expected: sbi does not contain `inout("a0")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes SBI register operands through the architecture runtime")
val sbi = file_read("src/os/kernel/arch/riscv64/sbi.spl")
expect(sbi).to_contain("extern fn rt_riscv64_sbi_call")
expect(sbi).to_contain("rt_riscv64_sbi_call(ext, fid, arg0, arg1, arg2, arg3, arg4, arg5)")
expect(sbi.contains("Identifier(\"arg0\")")).to_equal(false)
expect(sbi.contains("inout(\"a0\")")).to_equal(false)

val runtime = file_read("src/os/kernel/arch/riscv64/boot/freestanding_runtime.c")
expect(runtime).to_contain("RtRiscv64SbiRet rt_riscv64_sbi_call")
expect(runtime).to_contain("register spl_u64 a7 __asm__(\"a7\") = ext")

val linker = compiler_native_link_source()
expect(linker).to_contain("RtRiscv64SbiRet rt_riscv64_sbi_call")
```

</details>

#### keeps startup outside the RISC-V package closure and routes CMO operands through runtime

- keeps startup outside the RISC-V package closure and routes CMO operands through runtime
   - Expected: package does not contain `export plic, startup`
   - Expected: package does not contain `export _start, trap_handler`
   - Expected: cmo does not contain `in(reg)`
   - Expected: cmo does not contain `Identifier(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps startup outside the RISC-V package closure and routes CMO operands through runtime")
val hal_smp = file_read("src/os/kernel/arch/riscv64/hal_smp.spl")
val hal_cache = file_read("src/os/kernel/arch/riscv64/hal_cache.spl")
val user_entry = file_read("src/os/kernel/arch/riscv64/user_entry.spl")
expect(hal_smp).to_contain("baremetal.riscv.{sbi_probe_then_send_ipi}")
expect(hal_cache).to_contain("baremetal.riscv.{fence_i, cbo_flush, cbo_clean, cbo_inval}")
expect(user_entry).to_contain("baremetal.riscv.{fence_i}")

val package = file_read("src/lib/nogc_async_mut_noalloc/baremetal/riscv/__init__.spl")
expect(package.contains("export plic, startup")).to_equal(false)
expect(package.contains("export _start, trap_handler")).to_equal(false)

val cmo = file_read("src/lib/nogc_async_mut_noalloc/baremetal/riscv/cmo.spl")
expect(cmo).to_contain("extern fn rt_riscv64_cbo_clean")
expect(cmo).to_contain("rt_riscv64_cbo_flush(addr)")
expect(cmo.contains("in(reg)")).to_equal(false)
expect(cmo.contains("Identifier(")).to_equal(false)

val runtime = file_read("src/os/kernel/arch/riscv64/boot/freestanding_runtime.c")
expect(runtime).to_contain("void rt_riscv64_cbo_clean")
expect(runtime).to_contain(".option arch,+zicbom")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/userlib/riscv64_syscall_raw_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RISC-V64 raw syscall ABI contract.
- RISC-V64 raw syscall ABI contract

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

- Canonical SPipe generation for source `c7f13b33da5ad4a5e88d8ada32e6f897146e57904f3f86bb428abc26900124cb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c7f13b33da5ad4a5e88d8ada32e6f897146e57904f3f86bb428abc26900124cb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c7f13b33da5ad4a5e88d8ada32e6f897146e57904f3f86bb428abc26900124cb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/userlib/riscv64_syscall_raw_contract_spec.spl
mirror: doc/06_spec/01_unit/os/userlib/riscv64_syscall_raw_contract_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/userlib/riscv64_syscall_raw_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/userlib/riscv64_syscall_raw_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/userlib/riscv64_syscall_raw_contract_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes through the architecture runtime ecall shim' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/userlib/riscv64_syscall_raw_contract_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes CSR operands through immediate architecture runtime cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/userlib/riscv64_syscall_raw_contract_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes SBI register operands through the architecture runtime' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
