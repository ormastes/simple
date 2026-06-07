# Riscv Formal Contract Specification

> <details>

<!-- sdn-diagram:id=riscv_formal_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=riscv_formal_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

riscv_formal_contract_spec -> hardware
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=riscv_formal_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv Formal Contract Specification

## Scenarios

### RISC-V shared formal contract

#### uses 32-bit mask for rv32

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(riscv_mask_for_xlen(32)).to_equal(0xFFFFFFFF)
```

</details>

#### uses compressed instruction size when low bits are not 11

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(riscv_instruction_size(0x0001, true)).to_equal(2)
```

</details>

#### verifies a valid rv32 retire step

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = RiscvFormalContract.rv32_ghdl()
val event = RiscvRetireEvent.step(
    pc_before: 0x80010000,
    pc_after: 0x80010004,
    instr_bits: 0x00000513,
    rd_index: 10,
    rd_value: 0,
    x0_value: 0,
    privilege: RISCV_PRIV_MACHINE
)
expect(verify_riscv_event(contract, event).is_ok()).to_equal(true)
```

</details>

#### rejects x0 mutation

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = RiscvFormalContract.rv32_ghdl()
val event = RiscvRetireEvent.step(
    pc_before: 0x80010000,
    pc_after: 0x80010004,
    instr_bits: 0x00000013,
    rd_index: 0,
    rd_value: 1,
    x0_value: 1,
    privilege: RISCV_PRIV_MACHINE
)
val result = verify_riscv_event(contract, event)
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("x0")
```

</details>

#### rejects step pc mismatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = RiscvFormalContract.rv32_ghdl()
val event = RiscvRetireEvent.step(
    pc_before: 0x80010000,
    pc_after: 0x80010008,
    instr_bits: 0x00000513,
    rd_index: 10,
    rd_value: 0,
    x0_value: 0,
    privilege: RISCV_PRIV_MACHINE
)
val result = verify_riscv_event(contract, event)
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("pc_after")
```

</details>

#### rejects rv32 width overflow

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = RiscvFormalContract.rv32_ghdl()
val event = RiscvRetireEvent.step(
    pc_before: 0x80010000,
    pc_after: 0x80010004,
    instr_bits: 0x00000513,
    rd_index: 10,
    rd_value: 0x100000000,
    x0_value: 0,
    privilege: RISCV_PRIV_MACHINE
)
val result = verify_riscv_event(contract, event)
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("xlen 32")
```

</details>

#### verifies trap and return transitions for rv64

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = RiscvFormalContract.rv64_qemu()
val events = [
    RiscvRetireEvent.trap(
        pc_before: RV64_DEBUG_WRITE_ECALL_PC,
        trap_pc: 0x80200000,
        instr_bits: RISCV_ECALL_INSTR,
        privilege_before: RISCV_PRIV_USER,
        privilege_after: RISCV_PRIV_SUPERVISOR,
        trap_cause: RV64_CAUSE_ECALL_FROM_U
    ),
    RiscvRetireEvent.return_transfer(
        pc_before: 0x80200000,
        resume_pc: RV64_DEBUG_WRITE_RESUME_PC,
        privilege_before: RISCV_PRIV_SUPERVISOR,
        privilege_after: RISCV_PRIV_USER
    )
]
expect(verify_riscv_events(contract, events).is_ok()).to_equal(true)
```

</details>

#### rejects trap that does not raise privilege

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = RiscvFormalContract.rv64_qemu()
val event = RiscvRetireEvent.trap(
    pc_before: RV64_DEBUG_WRITE_ECALL_PC,
    trap_pc: 0x80200000,
    instr_bits: RISCV_ECALL_INSTR,
    privilege_before: RISCV_PRIV_USER,
    privilege_after: RISCV_PRIV_USER,
    trap_cause: RV64_CAUSE_ECALL_FROM_U
)
val result = verify_riscv_event(contract, event)
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("raise privilege")
```

</details>

#### rejects return that does not lower privilege

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = RiscvFormalContract.rv64_qemu()
val event = RiscvRetireEvent.return_transfer(
    pc_before: 0x80200000,
    resume_pc: RV64_DEBUG_WRITE_RESUME_PC,
    privilege_before: RISCV_PRIV_SUPERVISOR,
    privilege_after: RISCV_PRIV_SUPERVISOR
)
val result = verify_riscv_event(contract, event)
expect(result.is_err()).to_equal(true)
expect(result.unwrap_err()).to_contain("lower privilege")
```

</details>

### RISC-V formal helper integrations

#### verifies the default rv32 VHDL proof constraints

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(verify_rv32_default_vhdl_constraints().is_ok()).to_equal(true)
```

</details>

#### verifies the rv32 ghdl return-zero contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(verify_rv32_ghdl_return_zero_contract(0x80010000, 0).is_ok()).to_equal(true)
```

</details>

#### verifies rv64 qemu proof output markers with shared contract

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = "[KERNEL] trap vector installed\n[KERNEL] trap runtime installed\n[KERNEL] spawned user task id=1 entry=0x400000\n[KERNEL] entering U-mode at sepc=0x400000\nP\n[BOOT] RISC-V 64 boot complete\n"
expect(verify_rv64_qemu_user_proof_contract(output).is_ok()).to_equal(true)
```

</details>

#### reports missing external formal tools cleanly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = probe_riscv_external_formal()
expect(report.detail.len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/hardware/riscv_common/riscv_formal_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- RISC-V shared formal contract
- RISC-V formal helper integrations

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
