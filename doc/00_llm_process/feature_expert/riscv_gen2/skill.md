# RISC-V Gen2 feature expert

## Current boundary

Gen2 hardware lowers through typed HWIR and strict VHDL emission. Scalar
execution has monomorphized ALU/control/system/M/LSU providers, one completion
and retirement path. Versioned V9 additionally composes a dynamic IM tag-2
owner with a captured Zicsr tag-3 owner for the exact
`rv32im_zicsr_zifencei` and `rv64im_zicsr_zifencei` profiles.

The CSR projection accepts external `csr_present` and `csr_read_value` and emits
typed read/write intent only after instruction, register, privilege, address
class, presence, and read-only checks. A one-entry CSR owner captures that
intent and full completion, and V9 routes it through the common atomic
retirement path. Its public CSR lookup and commit qualifiers are fault-gated.
V9 generated-VHDL smoke scenarios cover captured reads, one commit, reset,
backpressure, and faults; this remains implementation evidence until an
admitted self-hosted CLI, formal/RVFI, and coverage gates are available.

## Canonical evidence

- Requirements: `doc/02_requirements/feature/riscv_gen2_hwir_foundation.md`
- Architecture: `doc/04_architecture/riscv_gen2_hwir_foundation.md`
- System plan: `doc/03_plan/sys_test/riscv_gen2_hwir_foundation.md`
- Scenario: `test/03_system/app/hardware/feature/riscv_gen2_csr_projection_spec.spl`
- Open CSR owner blocker:
  `doc/08_tracking/bug/riscv_gen2_atomic_csr_owner_missing_2026-08-12.md`
- V9 architecture and acceptance boundary:
  `doc/04_architecture/riscv_scalar_runtime_v9_im_zicsr.md`

Do not use bootstrap-seed results as qualification and do not advertise Zicsr,
full Zca, Linux, or a complete core from projection/row or bootstrap-only
evidence.
