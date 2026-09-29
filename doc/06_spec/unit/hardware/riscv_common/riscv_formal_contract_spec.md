# Riscv Formal Contract Specification

> Tests covering RISC-V shared formal contract, RISC-V formal helper integrations.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Riscv Formal Contract Specification

## Scenarios

### RISC-V shared formal contract

#### uses 32-bit mask for rv32

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- uses 32-bit mask for rv32
   - Expected: riscv_mask_for_xlen(32) equals `0xFFFFFFFF`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses 32-bit mask for rv32")
expect(riscv_mask_for_xlen(32)).to_equal(0xFFFFFFFF)
```

</details>

#### uses compressed instruction size when low bits are not 11

- uses compressed instruction size when low bits are not 11
   - Expected: riscv_instruction_size(0x0001, true) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses compressed instruction size when low bits are not 11")
expect(riscv_instruction_size(0x0001, true)).to_equal(2)
```

</details>

#### verifies a valid rv32 retire step

- verifies a valid rv32 retire step
   - Expected: verify_riscv_event(contract, event).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies a valid rv32 retire step")
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

- rejects x0 mutation
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects x0 mutation")
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

- rejects step pc mismatch
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects step pc mismatch")
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

- rejects rv32 width overflow
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects rv32 width overflow")
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

- verifies trap and return transitions for rv64
   - Expected: verify_riscv_events(contract, events).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies trap and return transitions for rv64")
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

- rejects trap that does not raise privilege
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects trap that does not raise privilege")
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

- rejects return that does not lower privilege
   - Expected: result.is_err() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects return that does not lower privilege")
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

- verifies the default rv32 VHDL proof constraints
   - Expected: verify_rv32_default_vhdl_constraints().is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies the default rv32 VHDL proof constraints")
expect(verify_rv32_default_vhdl_constraints().is_ok()).to_equal(true)
```

</details>

#### verifies the rv32 ghdl return-zero contract

- verifies the rv32 ghdl return-zero contract
   - Expected: verify_rv32_ghdl_return_zero_contract(0x80010000, 0).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies the rv32 ghdl return-zero contract")
expect(verify_rv32_ghdl_return_zero_contract(0x80010000, 0).is_ok()).to_equal(true)
```

</details>

#### verifies rv64 qemu proof output markers with shared contract

- verifies rv64 qemu proof output markers with shared contract
   - Expected: verify_rv64_qemu_user_proof_contract(output).is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies rv64 qemu proof output markers with shared contract")
val output = "[KERNEL] trap vector installed\n[KERNEL] trap runtime installed\n[KERNEL] spawned user task id=1 entry=0x400000\n[KERNEL] entering U-mode at sepc=0x400000\nP\n[BOOT] RISC-V 64 boot complete\n"
expect(verify_rv64_qemu_user_proof_contract(output).is_ok()).to_equal(true)
```

</details>

#### reports missing external formal tools cleanly

- reports missing external formal tools cleanly


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports missing external formal tools cleanly")
val report = probe_riscv_external_formal()
expect(report.detail.len()).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/hardware/riscv_common/riscv_formal_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering RISC-V shared formal contract, RISC-V formal helper integrations.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4719b610b009d14338c05b8831db91df5734eb5e51a12e7a75d3c18c8f527b2b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4719b610b009d14338c05b8831db91df5734eb5e51a12e7a75d3c18c8f527b2b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4719b610b009d14338c05b8831db91df5734eb5e51a12e7a75d3c18c8f527b2b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/hardware/riscv_common/riscv_formal_contract_spec.spl
mirror: doc/06_spec/unit/hardware/riscv_common/riscv_formal_contract_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/hardware/riscv_common/riscv_formal_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/hardware/riscv_common/riscv_formal_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/hardware/riscv_common/riscv_formal_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/hardware/riscv_common/riscv_formal_contract_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses 32-bit mask for rv32' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/riscv_common/riscv_formal_contract_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses compressed instruction size when low bits are not 11' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/hardware/riscv_common/riscv_formal_contract_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'verifies a valid rv32 retire step' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
