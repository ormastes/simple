<!-- codex-design -->
# RV64 Linux RTL Pipeline Design

Date: 2026-04-24

## Design Decisions

- Add `RiscvLinuxProfile`, `RiscvPlatformProfile`, and `Rv64LinuxBootArtifacts` in `hardware.riscv_common`.
- Add `RiscvTargetContract` in `compiler.backend.riscv_target`.
- Keep the existing RV64 hardware implementation intact where possible; add contract objects around it rather than rewriting internals.
- Reduce `FpgaPrepareManifest.default_xilinx()` to the RV64 lane so default generation stops implying first-class RV32 Linux CPU readiness.

## Test Design

- Hardware/common unit tests validate profile fields, ABI defaults, and required boot artifacts.
- RV64 orchestration tests validate readiness states, platform-derived manifest output, and non-misleading default output.
- LLVM/backend tests validate hosted and bare-metal triple selection plus explicit Linux ABI defaults.
- Native backend tests validate the shared contract values the RV32/RV64 paths now consume.
