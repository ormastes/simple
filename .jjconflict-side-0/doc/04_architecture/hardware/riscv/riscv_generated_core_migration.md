# RISC-V Generated Core Migration Architecture

Date: 2026-04-29

## Current Truth

- `src/hardware/fpga_linux/riscv_fpga_linux.spl` is the repo-native generated-core contract/orchestration layer for both generated Linux smoke lanes.
- `generated_rv32_linux` and `generated_rv64_linux` are the authoritative repo-native generated Linux proof lanes.
- External Linux RTL smokes remain optional reference diagnostics only:
  - `reference_external_rv32_linux` via LiteX/VexRiscv
  - `reference_external_rv64_linux` via CVA6
- The handwritten VHDL under `examples/09_embedded/fpga_riscv/rtl/` remains useful historical/reference material, but it is not the acceptance source of truth for repo-native generated Linux boot.
- The MLK-S02-100T board wrapper/products now exist as the first concrete board packaging target, but physical-board truth still depends on locally authoritative constraints, part selection, and vendor/programming files.

## Frozen Seam

The migration freezes one core-shell seam for generated CPU replacement:

- instruction fetch request/response
- data memory request/response with width, write strobes, misalignment, and fault signaling
- interrupt inputs
- trap/halt/debug outputs
- optional shell-owned bring-up services for semihost and mailbox

The public contract lives in `hardware.riscv_common.pkg.riscv_generated_core_pkg`.

## Proof Taxonomy

- `generated_rv32_linux` is the repo-native proof target for RV32 Linux; its emitted `rv32/rtl` bundle root is authoritative and its bounded generated GHDL proof gates are prerequisites to the shared Linux UART boot acceptance story.
- `generated_rv64_linux` is the repo-native proof target for RV64 Linux; its emitted `rv64/rtl` bundle root is authoritative and its bounded generated GHDL proof gates are prerequisites to the shared Linux UART boot acceptance story.
- `generated_rv32_baremetal` may remain as a narrower diagnostic lane, but it is not the acceptance source of truth for FPGA Linux bring-up.
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
