<!-- codex-research -->
# RISC-V FPGA Linux Domain Research

RISC-V Linux boot requires a firmware/kernel handoff with a valid hart id and device tree, plus a loadable kernel image with the RISC-V boot header. In this repo, both RV32 Linux and RV64 Linux are now authoritative generated Linux lanes. RV64 remains the more upstream-common MMU target, while RV32 remains valid here as a repo-owned generated lane rather than an experimental side path.

FPGA bring-up needs staged proof:

- RTL/simulation first: reset, fetch, UART, timer, interrupt, trap, MMU, DTB handoff.
- Synthesis/project generation next: deterministic Vivado TCL and constraints selected from a board profile.
- Hardware only after board details are known: part, clock, reset, DDR/BRAM map, UART pins, JTAG/programmer, and memory size.

For Xilinx, the repo should keep board-specific values outside CPU RTL generation so the same RV32/RV64 SoC lanes can be retargeted from a generic profile to the actual board profile. The MLK-S02-100T wrapper/products are now the first concrete board packaging target, but real hardware trust still depends on locally authoritative constraints, vendor files, and programming flow inputs.
