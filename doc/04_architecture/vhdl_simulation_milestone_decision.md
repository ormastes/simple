# VHDL Backend Simulation Milestone Decision

**Date:** 2026-04-04
**Status:** Decided
**Relates to:** `doc/03_plan/vhdl_backend_completion_plan_2026-04-04.md` Phase 7-8

## Decision

The VHDL backend completion milestone adopts **Option 1: Backend-complete, simulation-light**.

Generated VHDL is validated through GHDL analysis (`-a --std=08`) and elaboration (`-e --std=08`). Simulation-backed execution via the `riscv32_sim_vhdl` lane is **explicitly deferred** as a follow-on milestone.

## Rationale

1. **Backend correctness is the first-order goal.** GHDL analysis and elaboration prove that generated VHDL is syntactically and structurally valid IEEE 1076-2008. This is sufficient to move the backend from experimental to supported.

2. **The simulation lane has significant unfinished dependencies.** The `riscv32_sim_vhdl` plan (doc/03_plan/vhdl_backend_riscv_remote_interpreter_plan_2026-03-23.md) requires:
   - Hardware-defined RV32 CPU migrated to Simple source
   - Program image loading pipeline
   - Mailbox transport for simulation remote execution
   - `simple test` integration for the GHDL semihost runner
   - Host-side testbench improvements

   These are substantial, cross-cutting tasks that should not gate the backend completion milestone.

3. **Clean scoping prevents overclaiming.** By separating "valid VHDL generation" from "full simulation execution," the repo can make honest claims about backend support without implying capabilities that are still in development.

## riscv32_sim_vhdl Quarantine

The `riscv32_sim_vhdl` target lane is **quarantined** outside the VHDL backend completion milestone:

- **Not deleted.** The plan, documentation, and any partial implementation remain in the repo.
- **Not advertised.** README and backend docs do not list `riscv32_sim_vhdl` as a supported target.
- **Clearly scoped.** The RISCV plan (`doc/03_plan/vhdl_backend_riscv_remote_interpreter_plan_2026-03-23.md`) is the authoritative document for that work stream.
- **Future milestone.** When the simulation lane is complete, it becomes a separate milestone with its own verification evidence.

## What This Means for Backend Status

After this decision, the VHDL backend can be described as:

> Supported for a documented restricted hardware subset. Strict and fail-fast on unsupported constructs. Validated through GHDL analysis/elaboration. Simulation support is scoped to a follow-on milestone.

## Follow-On Work

When the simulation milestone is pursued, it should:
1. Use backend-generated VHDL (not handwritten RTL) as the hardware source
2. Prove at least one generated design runs in GHDL simulation
3. Integrate with `simple test` for automated pass/fail reporting
4. Update the support matrix to reflect simulation status

## See Also

- `doc/03_plan/vhdl_backend_completion_plan_2026-04-04.md` — Overall completion plan
- `doc/03_plan/vhdl_backend_riscv_remote_interpreter_plan_2026-03-23.md` — RISCV simulation plan
- `doc/04_architecture/vhdl_hardware_subset_contract.md` — Supported subset contract
- `doc/04_architecture/vhdl_support_matrix.md` — Support matrix
