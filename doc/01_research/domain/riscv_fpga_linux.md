<!-- codex-research -->
# RISC-V FPGA Linux Domain Research

RISC-V Linux boot requires a firmware/kernel handoff with a valid hart id and device tree, plus a loadable kernel image with the RISC-V boot header. RV64 Linux is the primary upstream-compatible target for a normal MMU-enabled Linux bring-up. RV32 Linux is treated here as an experimental lane because it depends on a supplied kernel/toolchain/rootfs source rather than the repo's existing upstream-like RV64 path.

FPGA bring-up needs staged proof:

- RTL/simulation first: reset, fetch, UART, timer, interrupt, trap, MMU, DTB handoff.
- Synthesis/project generation next: deterministic Vivado TCL and constraints selected from a board profile.
- Hardware only after board details are known: part, clock, reset, DDR/BRAM map, UART pins, JTAG/programmer, and memory size.

For Xilinx, the repo should keep board-specific values outside CPU RTL generation so the same RV32/RV64 SoC lanes can be retargeted from a generic profile to the actual board profile.
