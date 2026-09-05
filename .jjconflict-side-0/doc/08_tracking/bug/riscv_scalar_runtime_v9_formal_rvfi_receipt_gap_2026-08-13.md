# V9 scalar runtime lacks solver-backed RVFI receipts

- Status: implementation scaffold complete; external formal evidence blocked.
- Owner: RISC-V Gen2 formal/backend lane.
- Scope: V9 `rv32im_zicsr_zifencei` and `rv64im_zicsr_zifencei` only.

## Current boundary

`riscv_scalar_runtime_pipeline_v9_rvfi_to_vhdl.spl` is a canonical retirement
observer: it renders the V9 graph, captures instruction/source evidence at the
accepted input edge, and maps the held completion record to RVFI. Its GHDL
smoke checks RV32/RV64 x0-source normalization and ordered retirements.

This is not formal proof. The older RVFI protocol is bounded to RV32 ADD and
its `check-riscv-formal-dual-track.shs` aggregate does not execute V9 jobs.

## Required unblock

Create a V9-specific formal artifact producer and runner with profile-bound
prove, cover, and expected-failing mutation jobs. Every external receipt must
bind the canonical V9 graph/VHDL/RVFI-contract hashes and exact tool versions.
Properties must cover retirement/order/stability/fault containment, full-M
including divide corners, CSR policy and exact-once commit, and FENCE effects.
RVFI interrupt remains an explicit unsupported assumption until V9 gains a
real interrupt source.

## Resume

After an admitted self-hosted CLI is deployed, run the V9 RVFI GHDL fixture
once and then the new V9-specific formal runner with Yosys/GHDL/SymbiYosys and
Boolector receipts. Do not substitute bootstrap output or the legacy ADD-only
aggregate for these jobs.
