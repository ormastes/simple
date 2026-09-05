# Riscv Target Specification

> Tests covering RISC-V backend target contracts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv Target Specification

## Scenarios

### RISC-V backend target contracts

#### defines RV64 Linux as riscv64-unknown-linux-gnu LP64D rv64gc

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines RV64 Linux as riscv64-unknown-linux-gnu LP64D rv64gc
   - Expected: contract.triple() equals `riscv64-unknown-linux-gnu`
   - Expected: contract.abi.to_text() equals `lp64d`
   - Expected: contract.march equals `rv64gc`
   - Expected: contract.abi_flag() equals `-mabi=lp64d`
   - Expected: contract.march_flag() equals `-march=rv64gc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines RV64 Linux as riscv64-unknown-linux-gnu LP64D rv64gc")
val contract = riscv_linux_target_contract(CodegenTarget.Riscv64)
expect(contract.triple()).to_equal("riscv64-unknown-linux-gnu")
expect(contract.abi.to_text()).to_equal("lp64d")
expect(contract.march).to_equal("rv64gc")
expect(contract.abi_flag()).to_equal("-mabi=lp64d")
expect(contract.march_flag()).to_equal("-march=rv64gc")
```

</details>

#### defines RV32 Linux as riscv32-unknown-linux-gnu ILP32D rv32gc

- defines RV32 Linux as riscv32-unknown-linux-gnu ILP32D rv32gc
   - Expected: contract.triple() equals `riscv32-unknown-linux-gnu`
   - Expected: contract.abi.to_text() equals `ilp32d`
   - Expected: contract.march equals `rv32gc`
   - Expected: contract.pointer_bits equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines RV32 Linux as riscv32-unknown-linux-gnu ILP32D rv32gc")
val contract = riscv_linux_target_contract(CodegenTarget.Riscv32)
expect(contract.triple()).to_equal("riscv32-unknown-linux-gnu")
expect(contract.abi.to_text()).to_equal("ilp32d")
expect(contract.march).to_equal("rv32gc")
expect(contract.pointer_bits).to_equal(32)
```

</details>

#### keeps compiler and hardware aligned on the RV32 Linux contract

- keeps compiler and hardware aligned on the RV32 Linux contract
   - Expected: compiler_contract.pointer_bits equals `platform.linux.xlen`
   - Expected: compiler_contract.abi equals `platform.linux.abi`
   - Expected: platform.name equals `qemu_virt_rv32`
   - Expected: platform.linux.mmu_mode.to_text() equals `sv32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps compiler and hardware aligned on the RV32 Linux contract")
val compiler_contract = riscv_linux_target_contract(CodegenTarget.Riscv32)
val platform = qemu_virt_rv32_platform_profile()
expect(compiler_contract.pointer_bits).to_equal(platform.linux.xlen)
expect(compiler_contract.abi).to_equal(platform.linux.abi)
expect(platform.name).to_equal("qemu_virt_rv32")
expect(platform.linux.mmu_mode.to_text()).to_equal("sv32")
```

</details>

#### keeps compiler and hardware aligned on the RV64-first Linux contract

- keeps compiler and hardware aligned on the RV64-first Linux contract
   - Expected: compiler_contract.pointer_bits equals `platform.linux.xlen`
   - Expected: compiler_contract.abi equals `platform.linux.abi`
   - Expected: platform.name equals `qemu_virt_rv64`
   - Expected: platform.linux.mmu_mode.to_text() equals `sv39`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps compiler and hardware aligned on the RV64-first Linux contract")
val compiler_contract = riscv_linux_target_contract(CodegenTarget.Riscv64)
val platform = qemu_virt_rv64_platform_profile()
expect(compiler_contract.pointer_bits).to_equal(platform.linux.xlen)
expect(compiler_contract.abi).to_equal(platform.linux.abi)
expect(platform.name).to_equal("qemu_virt_rv64")
expect(platform.linux.mmu_mode.to_text()).to_equal("sv39")
```

</details>

#### keeps bare-metal contracts on none-elf triples

- keeps bare-metal contracts on none-elf triples
   - Expected: contract.triple() equals `riscv64-unknown-none-elf`
   - Expected: contract.sysroot equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps bare-metal contracts on none-elf triples")
val contract = riscv_baremetal_target_contract(CodegenTarget.Riscv64)
expect(contract.triple()).to_equal("riscv64-unknown-none-elf")
expect(contract.sysroot).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/backend/riscv_target_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RISC-V backend target contracts.
- RISC-V backend target contracts

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

- Canonical SPipe generation for source `3eb88fd13cd92acde9b9e7fa648fd9ce9aed114d6b31589afd656fbab730c2ca`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3eb88fd13cd92acde9b9e7fa648fd9ce9aed114d6b31589afd656fbab730c2ca`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3eb88fd13cd92acde9b9e7fa648fd9ce9aed114d6b31589afd656fbab730c2ca`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/compiler/backend/riscv_target_spec.spl
mirror: doc/06_spec/unit/compiler/backend/riscv_target_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/backend/riscv_target_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/backend/riscv_target_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/backend/riscv_target_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/backend/riscv_target_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines RV64 Linux as riscv64-unknown-linux-gnu LP64D rv64gc' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/riscv_target_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines RV32 Linux as riscv32-unknown-linux-gnu ILP32D rv32gc' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/backend/riscv_target_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps compiler and hardware aligned on the RV32 Linux contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
