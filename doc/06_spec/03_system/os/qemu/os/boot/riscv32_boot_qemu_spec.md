# Riscv32 Boot Qemu Specification

> Tests covering RISC-V 32 Architecture Boot.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv32 Boot Qemu Specification

## Scenarios

### RISC-V 32 Architecture Boot

<details>
<summary>Advanced: binds the canonical RV32 boot artifact contract</summary>

#### binds the canonical RV32 boot artifact contract _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- binds the canonical RV32 boot artifact contract
   - Expected: target.arch equals `Architecture.Riscv32`
   - Expected: target.entry equals `src/os/kernel/arch/riscv32/boot.spl`
   - Expected: target.linker_script equals `src/os/kernel/arch/riscv32/linker.ld`
   - Expected: target.target_triple equals `riscv32-unknown-none`
   - Expected: target.output equals `build/os/simpleos_riscv32.elf`
   - Expected: target.qemu_system equals `qemu-system-riscv32`
   - Expected: target.qemu_machine equals `virt`
   - Expected: target.qemu_cpu equals `rv32`
   - Expected: target.qemu_memory equals `128M`
   - Expected: target.qemu_bios equals `none`
   - Expected: target.qemu_extra.len() equals `0`
   - Expected: rt_file_exists(target.output) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binds the canonical RV32 boot artifact contract")
val target = get_target(ARCH)
expect(target.arch).to_equal(Architecture.Riscv32)
expect(target.entry).to_equal("src/os/kernel/arch/riscv32/boot.spl")
expect(target.linker_script).to_equal("src/os/kernel/arch/riscv32/linker.ld")
expect(target.target_triple).to_equal("riscv32-unknown-none")
expect(target.output).to_equal("build/os/simpleos_riscv32.elf")
expect(target.qemu_system).to_equal("qemu-system-riscv32")
expect(target.qemu_machine).to_equal("virt")
expect(target.qemu_cpu).to_equal("rv32")
expect(target.qemu_memory).to_equal("128M")
expect(target.qemu_bios).to_equal("none")
expect(target.qemu_extra.len()).to_equal(0)
expect(rt_file_exists(target.output)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: UART initialized in direct boot</summary>

#### UART initialized in direct boot _(slow)_

- UART initialized in direct boot


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("UART initialized in direct boot")
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("UART")
```

</details>


</details>

<details>
<summary>Advanced: prints RISC-V 32 architecture identifier</summary>

#### prints RISC-V 32 architecture identifier _(slow)_

- prints RISC-V 32 architecture identifier


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("prints RISC-V 32 architecture identifier")
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("RISC-V 32")
```

</details>


</details>

<details>
<summary>Advanced: memory map parsed</summary>

#### memory map parsed _(slow)_

- memory map parsed


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("memory map parsed")
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("Memory map")
```

</details>


</details>

<details>
<summary>Advanced: RAM at 0x80000000</summary>

#### RAM at 0x80000000 _(slow)_

- RAM at 0x80000000


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("RAM at 0x80000000")
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("0x80000000")
```

</details>


</details>

<details>
<summary>Advanced: boot sequence completes</summary>

#### boot sequence completes _(slow)_

- boot sequence completes


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boot sequence completes")
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("boot complete")
```

</details>


</details>

<details>
<summary>Advanced: initializes noalloc boot memory services</summary>

#### initializes noalloc boot memory services _(slow)_

- initializes noalloc boot memory services


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("initializes noalloc boot memory services")
if _can_run():
    val output = _run_qemu_cached()
    expect(output).to_contain("LOG OK")
    expect(output).to_contain("MEM OK")
    expect(output).to_contain("PMM OK")
    expect(output).to_contain("HEAP OK")
    expect(output).to_contain("SVC OK")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/boot/riscv32_boot_qemu_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RISC-V 32 Architecture Boot.
- RISC-V 32 Architecture Boot

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 7 |
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

- Canonical SPipe generation for source `f1b8018ca2d47a1952cc14407800c9dfd36fa7f1ce63915a2978f1bf6f1ce581`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f1b8018ca2d47a1952cc14407800c9dfd36fa7f1ce63915a2978f1bf6f1ce581`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f1b8018ca2d47a1952cc14407800c9dfd36fa7f1ce63915a2978f1bf6f1ce581`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/os/qemu/os/boot/riscv32_boot_qemu_spec.spl
mirror: doc/06_spec/03_system/os/qemu/os/boot/riscv32_boot_qemu_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/qemu/os/boot/riscv32_boot_qemu_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/qemu/os/boot/riscv32_boot_qemu_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/qemu/os/boot/riscv32_boot_qemu_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/qemu/os/boot/riscv32_boot_qemu_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'binds the canonical RV32 boot artifact contract' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/boot/riscv32_boot_qemu_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'UART initialized in direct boot' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/qemu/os/boot/riscv32_boot_qemu_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prints RISC-V 32 architecture identifier' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
