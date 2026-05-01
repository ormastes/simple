<!-- codex-design -->
# RISC-V Generated Core Migration Design

Date: 2026-04-29

## Design Decisions

- Add a shared `RiscvProofLane` enum so generated proof and external reference proof cannot be conflated in manifests, generated VHDL comments, or smoke scripts.
- Add shared shell-seam structs for fetch, memory, trap status, and boot handoff in `hardware.riscv_common.pkg.riscv_generated_core_pkg`.
- Keep `hardware.fpga_linux.riscv_fpga_linux` as orchestration and metadata generation for runnable generated Linux RTL bundles; the emitted `rv32/rtl` and `rv64/rtl` roots are the authoritative generated-core handoff surfaces.
- Mark the repo-native RV32 lane as `generated_rv32_linux` with generated Linux handoff/DTB metadata rather than a baremetal-only proof label.
- Mark the repo-native RV64 lane as `generated_rv64_linux` with `FW_JUMP`/`a0`/`a1` boot-contract metadata.
- Relabel LiteX/VexRiscv and CVA6 smokes as `reference_external_*` so script output is truthful and clearly non-mandatory for acceptance.
- Carry MLK-S02-100T board-specific packaging as explicit `mlk_s02_100t_rv32_linux` and `mlk_s02_100t_rv64_linux` products while keeping final physical trust anchored to local authoritative constraints/vendor files.

## Verification Design

- Unit tests cover proof-lane labeling, shell-service boundaries, and RV32/RV64 acceptance markers.
- Existing FPGA/Linux manifest tests now assert proof-lane metadata in readiness summaries and generated bundle manifests.
- Script verification covers generated-lane labeling and bundle contracts; external RTL scripts remain optional diagnostics and do not gate generated-only acceptance.
