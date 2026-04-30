# RISC-V Generated Core Migration Architecture

Date: 2026-04-29

## Current Truth

- The only in-repo runnable RTL CPU lane is the handwritten RV32I VHDL core under `examples/09_embedded/fpga_riscv/rtl/`.
- `src/hardware/fpga_linux/riscv_fpga_linux.spl` is the repo-native generated-core contract/orchestration layer for the generated RV64 Linux smoke lane.
- Linux RTL smokes remain external reference lanes:
  - `reference_external_rv32_linux` via LiteX/VexRiscv
  - `reference_external_rv64_linux` via CVA6
- The repo-native `generated_rv64_linux` lane is now the primary generated Linux proof path; CVA6 remains a required cross-check, not a substitute.

## Frozen Seam

The migration freezes one core-shell seam for generated CPU replacement:

- instruction fetch request/response
- data memory request/response with width, write strobes, misalignment, and fault signaling
- interrupt inputs
- trap/halt/debug outputs
- optional shell-owned bring-up services for semihost and mailbox

The public contract lives in `hardware.riscv_common.pkg.riscv_generated_core_pkg`.

## Proof Taxonomy

- `generated_rv32_baremetal` is the repo-native proof target for RV32 first.
- `generated_rv64_linux` is the repo-native proof target for RV64 Linux and is validated by generated GHDL UART boot markers.
- `generated_rv32_linux` remains an optional later lane.
- External LiteX/CVA6 lanes never count as generated-core proof.

## Migration Rule

Keep the shell stable and replace internals incrementally:

1. generated decode/helper overlays
2. generated ALU/branch/control-flow logic
3. generated regfile
4. generated load/store datapath
5. generated trap/halt dispatch
6. generated top-level RV32 core

Semihost and mailbox may remain shell services until the generated CPU claim is already true.
