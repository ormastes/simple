<!-- codex-design -->
# RISC-V Generated Core Migration Design

Date: 2026-04-29

## Design Decisions

- Add a shared `RiscvProofLane` enum so generated proof and external reference proof cannot be conflated in manifests, generated VHDL comments, or smoke scripts.
- Add shared shell-seam structs for fetch, memory, trap status, and boot handoff in `hardware.riscv_common.pkg.riscv_generated_core_pkg`.
- Keep `hardware.fpga_linux.riscv_fpga_linux` as orchestration and metadata generation only; it now emits proof-lane and shell-contract metadata rather than implying runnable generated Linux RTL.
- Mark the repo-native RV32 lane as `generated_rv32_baremetal` and keep semihost/mailbox explicitly outside the generated-core claim boundary.
- Mark the repo-native RV64 lane as `generated_rv64_linux` with `FW_JUMP`/`a0`/`a1` boot-contract metadata.
- Relabel LiteX/VexRiscv and CVA6 smokes as `reference_external_*` so script output is truthful.

## Verification Design

- Unit tests cover proof-lane labeling, shell-service boundaries, and RV32/RV64 acceptance markers.
- Existing FPGA/Linux manifest tests now assert proof-lane metadata in readiness summaries and generated bundle manifests.
- Script verification is syntax-level plus output relabeling; these changes do not attempt to prove generated Linux boot yet.
