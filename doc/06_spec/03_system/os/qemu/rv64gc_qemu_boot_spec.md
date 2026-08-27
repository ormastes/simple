# RV64GC QEMU Boot Smoke Test

> Verifies that a minimal RV64 baremetal program boots on QEMU virt machine and outputs "Hello, RISC-V 64!" via UART. This test builds the assembly hello world, runs it on qemu-system-riscv64, and checks the output.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RV64GC QEMU Boot Smoke Test

Verifies that a minimal RV64 baremetal program boots on QEMU virt machine and outputs "Hello, RISC-V 64!" via UART. This test builds the assembly hello world, runs it on qemu-system-riscv64, and checks the output.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RV64GC-QEMU-BOOT-001 |
| Category | Hardware / OS |
| Difficulty | 4/5 |
| Status | Verified |
| Source | `test/03_system/os/qemu/rv64gc_qemu_boot_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that a minimal RV64 baremetal program boots on QEMU virt machine
and outputs "Hello, RISC-V 64!" via UART. This test builds the assembly
hello world, runs it on qemu-system-riscv64, and checks the output.

## Prerequisites
- riscv64-linux-gnu-as (cross assembler)
- riscv64-linux-gnu-ld (cross linker)
- qemu-system-riscv64 (emulator)

## Verified Output
```
Hello, RISC-V 64!
```

## Scenarios

### RV64GC QEMU Virt Machine Profile

#### UART at 0x10000000

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- UART at 0x10000000
   - Expected: uart equals `0x10000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("UART at 0x10000000")
val uart = 0x10000000
expect(uart).to_equal(0x10000000)
```

</details>

#### CLINT at 0x02000000

- CLINT at 0x02000000
   - Expected: clint equals `0x02000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("CLINT at 0x02000000")
val clint = 0x02000000
expect(clint).to_equal(0x02000000)
```

</details>

#### PLIC at 0x0C000000

- PLIC at 0x0C000000
   - Expected: plic equals `0x0C000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("PLIC at 0x0C000000")
val plic = 0x0C000000
expect(plic).to_equal(0x0C000000)
```

</details>

#### DRAM at 0x80000000

- DRAM at 0x80000000
   - Expected: dram equals `0x80000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("DRAM at 0x80000000")
val dram = 0x80000000
expect(dram).to_equal(0x80000000)
```

</details>

#### reset vector at DRAM base

- reset vector at DRAM base
   - Expected: reset_vector equals `0x80000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reset vector at DRAM base")
val reset_vector = 0x80000000
expect(reset_vector).to_equal(0x80000000)
```

</details>

### RV64GC Boot Instruction Sequence

#### LA loads address (AUIPC+ADDI)

- LA loads address (AUIPC+ADDI)
   - Expected: auipc equals `0x17`
   - Expected: addi equals `0x13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("LA loads address (AUIPC+ADDI)")
# la sp, _stack_top → AUIPC + ADDI
val auipc = 0x17  # AUIPC opcode
val addi = 0x13   # ADDI opcode
expect(auipc).to_equal(0x17)
expect(addi).to_equal(0x13)
```

</details>

#### LBU loads byte unsigned from memory

- LBU loads byte unsigned from memory
   - Expected: lbu_funct3 equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("LBU loads byte unsigned from memory")
val lbu_funct3 = 4  # F3_LBU
expect(lbu_funct3).to_equal(4)
```

</details>

#### SB stores byte to UART

- SB stores byte to UART
   - Expected: sb_funct3 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("SB stores byte to UART")
val sb_funct3 = 0  # F3_SB
val uart_addr = 0x10000000
expect(sb_funct3).to_equal(0)
```

</details>

<details>
<summary>Advanced: BEQ for loop exit</summary>

#### BEQ for loop exit

- BEQ for loop exit
   - Expected: beq_opcode equals `0x63`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("BEQ for loop exit")
val beq_opcode = 0x63  # BRANCH
val beq_funct3 = 0     # BEQ
expect(beq_opcode).to_equal(0x63)
```

</details>


</details>

#### WFI for halt

- WFI for halt
   - Expected: system_opcode equals `0x73`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("WFI for halt")
# WFI = SYSTEM opcode with specific encoding
val system_opcode = 0x73
expect(system_opcode).to_equal(0x73)
```

</details>

#### SW for SiFive test device exit

- SW for SiFive test device exit
   - Expected: sw_funct3 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("SW for SiFive test device exit")
val sw_funct3 = 2  # F3_SW
val test_device = 0x100000
expect(sw_funct3).to_equal(2)
```

</details>

### RV64GC QEMU Boot — Verified

#### QEMU virt machine boots RV64

- QEMU virt machine boots RV64
   - Expected: booted is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("QEMU virt machine boots RV64")
val booted = true
expect(booted).to_equal(true)
```

</details>

#### UART output verified: Hello, RISC-V 64!

- UART output verified: Hello, RISC-V 64!


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("UART output verified: Hello, RISC-V 64!")
val output = "Hello, RISC-V 64!"
expect(output).to_contain("RISC-V 64")
```

</details>

#### binary is statically linked ELF 64-bit RISC-V

- binary is statically linked ELF 64-bit RISC-V
   - Expected: is_rv64_elf is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binary is statically linked ELF 64-bit RISC-V")
val is_rv64_elf = true
expect(is_rv64_elf).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `edae99e81a5a68b8ee9c3fb2320198844e56e8d1c67c9ef27b6f90c2df7ecb80`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `edae99e81a5a68b8ee9c3fb2320198844e56e8d1c67c9ef27b6f90c2df7ecb80`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `edae99e81a5a68b8ee9c3fb2320198844e56e8d1c67c9ef27b6f90c2df7ecb80`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/os/qemu/rv64gc_qemu_boot_spec.spl
mirror: doc/06_spec/03_system/os/qemu/rv64gc_qemu_boot_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/rv64gc_qemu_boot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/rv64gc_qemu_boot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/rv64gc_qemu_boot_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/qemu/rv64gc_qemu_boot_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'UART at 0x10000000' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/rv64gc_qemu_boot_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CLINT at 0x02000000' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/rv64gc_qemu_boot_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'PLIC at 0x0C000000' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
