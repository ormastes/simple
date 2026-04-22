# RV32 RTL Linux Reference Lock

Backend: `litex-vexriscv-verilator`

Repository: `https://github.com/litex-hub/linux-on-litex-vexriscv.git`

Pinned revision: `7a871494ab9719baedb3ae25a731e33756fd20d8`

Local cache path: `build/third_party/rtl/linux-on-litex-vexriscv`

Runner: `scripts/rtl_riscv32_linux_litex.shs`

Success markers:

- `Linux version`
- one of `Freeing unused kernel memory`, `Run /sbin/init`, `BusyBox`, or `login:`

Notes:

- This is the first RV32 local RTL Linux boot reference lane.
- It proves a local RTL/Verilator Linux boot, not repo-native Simple RTL Linux boot.
- The repo-native RV32 FPGA shell remains generated separately by `examples/09_embedded/fpga_riscv/generate_linux_rtl.spl`.
