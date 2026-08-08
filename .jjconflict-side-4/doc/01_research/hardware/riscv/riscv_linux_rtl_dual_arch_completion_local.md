# RISC-V Linux RTL Dual-Arch Completion — Domain Research

- Linux on RISC-V expects a stable machine contract centered on `a0 = hartid`, `a1 = dtb`, and `satp = 0` until the kernel installs paging.
- QEMU `virt` is the least divergent first contract for both RV32 and RV64 because CLINT/PLIC/UART/DRAM placement is already standardized in the existing smoke lanes.
- RV64 Linux normally targets Sv39 + LP64D and RV32 Linux targets Sv32 + ILP32D.
- External RTL lanes are useful final evidence, but they validate architecture compatibility, not by themselves the existence of repo-native CPU trees.
