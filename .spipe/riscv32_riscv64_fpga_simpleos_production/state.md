# Feature: riscv32_riscv64_fpga_simpleos_production

## Raw Request
make simple riscv 64 and 32 production level, let run simple os on both of then with fpga

## Task Type
feature

## Refined Goal
Make RV32 and RV64 SimpleOS FPGA support production-ready with repeatable local, RTL, QEMU, and physical-board evidence.

## Acceptance Criteria
- AC-1: RV32 and RV64 RTL smoke gates report both lanes in one run.
- AC-2: RV32 and RV64 SimpleOS build/run evidence exists and is current.
- AC-3: FPGA preflight reports tool, board, artifact, JTAG, UART, and bitstream status.
- AC-4: Physical FPGA boot is not marked done until a board bitstream, load path, UART marker, and SimpleOS payload all pass.
- AC-5: Current blockers are recorded in `doc/09_report/`.

## Scope Exclusions
Do not invent a second RISC-V core, bootloader, or FPGA framework. Reuse the existing RV32/RV64 RTL, SimpleOS QEMU, and Kria/K26 preflight scripts.

## Cooperative Review
N/A for this slice: this turn only fixes existing smoke wrappers and records blockers. Broad production completion still needs sidecar lanes for RV32, RV64, FPGA hardware, and SimpleOS boot.

## Evidence 2026-07-03
- `SIMPLE_BINARY=bin/release/simple sh scripts/check/check-riscv64-fpga-simpleos-preflight.shs --local-only`:
  - PASS: FT4232H USB present, serial ports present, JTAG interface free, openFPGALoader, OpenOCD, Vivado, RISC-V cross compilers, RV64 SimpleOS ELF artifact, RV64 SimpleOS bin artifact, RV64 bitstream artifact, Simple hello.
  - FAIL: yosys, RV64 FPGA core executable gate, RV64 FPGA ELF load-context gate.
  - RV64 core reason: `build/vhdl/rv64/rv64gc_core.vhd` is a placeholder core with no instruction execution or debug/load context.
  - RV64 load reason: `build/fpga/k26/load_elf_k26.log` records XSDB `dow` failure with `Invalid context`.
- `SIMPLE_BINARY=bin/release/simple bash scripts/fpga/build_k26_vexriscv.shs`:
  - NOW FAIL-FAST: the wrapper regenerates `build/vhdl/rv64/rv64gc_core.vhd`, detects placeholder RTL, and exits before Vivado unless `ALLOW_PLACEHOLDER_RTL=1` is set for plumbing diagnostics.
  - PRIOR PASS: with placeholder RTL allowed, Vivado synthesis, implementation, DRC, and bitgen completed and copied `build/fpga/k26/k26_vexriscv.bit` plus `build/build/xilinx_kv260/gateware/xilinx_kv260.bit`.
- `SIMPLE_BINARY=bin/release/simple CAPTURE_SECONDS=5 LINUX_TIMEOUT=10 sh scripts/fpga/check_kv260_simple_rv64_linux.shs`:
  - PASS: RV64 bitstream and ELF artifacts present, ELF header is ELF64 RISC-V, KV260 bitstream loads, merged USB PS UART responds, and generated RV64 Linux handoff passes.
  - INFO: PL UART on merged USB has no output; current generated image still needs PMOD UART capture or a routed UART before SimpleOS payload execution can be proven.
- `bash scripts/fpga/load_elf_k26.shs`:
  - PASS: programs the generated K26 bitstream.
  - FAIL: XSDB `dow build/os/simpleos_riscv64_fpga.elf` returns `Invalid context`, so the current generated bitstream has no usable CPU/debug context for ELF download.
- `SIMPLE_OS_BUILD_BACKEND=cranelift bin/release/simple os build --arch=riscv64 --scenario=riscv64-fpga-mmode`:
  - PASS: builds `build/os/simpleos_riscv64_fpga.elf` and auto-objcopies `build/rv64_bringup_check/hello_litex_rv64.bin`.
- `SIMPLE_OS_BUILD_BACKEND=cranelift bin/release/simple os build --arch=riscv32 --scenario=riscv32-fpga-mmode`:
  - FAIL: correctly resolves `build/os/simpleos_riscv32_fpga.elf`, but this host's release Simple binary reports `Cranelift native builds do not support hosted riscv32 yet; use --backend llvm for this lane`; no LLVM-enabled Simple binary exists in this workspace.
- `env LLVM_SYS_180_PREFIX=/usr SIMPLE_LIB=src SIMPLE_BINARY=src/compiler_rust/target/debug/simple SIMPLE_OS_BUILD_BACKEND=llvm src/compiler_rust/target/debug/simple os build --scenario=riscv32-fpga-mmode`:
  - PASS: builds `build/os/simpleos_riscv32_fpga.elf` and auto-objcopies `build/rv32_bringup_check/hello_litex_rv32.bin` with the local LLVM-enabled Rust Simple driver.
- `sh scripts/check/check-riscv-rtl-linux-smoke.shs --timeout=10`:
  - PASS `generated_rv32_linux`: GHDL reports `GENERATED_RV32_LINUX_HANDOFF: PASS`.
  - PASS `generated_rv64_linux`: GHDL reports `GENERATED_RV64_LINUX_HANDOFF: PASS`.
- `bin/release/simple run src/hardware/fpga_linux/generate_riscv_fpga_bundle.spl /tmp/simple_riscv_bundle_check`:
  - PASS: emits RV32 and RV64 generated-core bundle files under `rv32/rtl` and `rv64/rtl`, including core source, VHDL package/core, debug sidecar, and Linux handoff testbench artifacts.
- `SIMPLE_BINARY=bin/release/simple sh scripts/check/check-riscv-fpga-simpleos-preflight.shs --local-only`:
  - Reuses the RV64 preflight and additionally reports RV32 ELF, bin, and bitstream artifact status.
  - PASS: RV32 ELF and bin artifacts exist.
  - FAIL: RV32 bitstream artifact is absent in this workspace.
  - FAIL: RV32 FPGA core executable evidence is absent (`build/vhdl/rv32/rv32_core.vhd` missing).
  - FAIL: RV32 FPGA ELF load/run evidence is absent (`build/fpga/rv32/load_elf_rv32.log` missing).

## Phase
dev-in-progress

## Log
- dev: Created production-readiness lane and fixed existing smoke wrappers to expose both RV32/RV64 missing smoke artifacts.
- dev: Added dual-arch FPGA preflight wrapper so RV32 artifacts are checked beside the existing RV64 preflight.
- dev: Added a minimal bundle generator CLI, routed generated Linux runners through `GEN_DIR/rv32/rtl` and `GEN_DIR/rv64/rtl`, and made the bundle generator fail closed on missing copied RTL sources.
- dev: Replaced the bundle generator's copied RTL dependency with emitted generated-core bundle artifacts, so bundle generation succeeds without `examples/09_embedded/fpga_riscv/rtl`.
- dev: Added minimal RV32/RV64 smoke payloads and removed the stale RV64 native-build gate, so the top-level generated RTL Linux smoke passes both lanes.
- dev: Exposed RV64/RV32 FPGA M-mode lanes through `simple os build --scenario=...`, fixed the RV64 FPGA entry symbol, added freestanding not-found runtime hooks, and auto-derived the RV64 raw FPGA payload bin from the built ELF. RV32 is wired but needs an LLVM-enabled Simple compiler on this host.
- dev: Repaired the K26 RV64 VHDL/Vivado wrapper, generated and programmed a current KV260 bitstream, and recorded that physical programming now passes while SimpleOS softcore UART execution remains unproven.
- dev: Updated the K26 ELF load helper to use the current RV64 FPGA ELF and preserve XSDB logs; current physical load is blocked by missing CPU/debug context in the generated bitstream.
- dev: Added fail-closed RV64 core/load-context gates to FPGA preflight so a present-but-placeholder bitstream cannot satisfy production readiness.
- dev: Built RV32 SimpleOS FPGA ELF/bin with the local LLVM-enabled Rust Simple driver; RV32 remains blocked on a real bitstream.
- dev: Added fail-closed RV32 core/load-context gates so future RV32 bitstreams also need executable-core and payload-load evidence.
- dev: Made the K26 RV64 bitstream wrapper fail fast on placeholder core RTL so stale/generated bitstreams cannot be refreshed as production evidence.
