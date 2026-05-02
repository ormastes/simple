# RV64 RTL Linux Reference Lock

Backend: `cva6-verilator`

Repository: `https://github.com/openhwgroup/cva6.git`

Pinned revision: `8e694e6460d017fb8a175336cd7dcb91d8eff682`

Local cache path: `build/third_party/rtl/cva6`

Runner: `scripts/rtl_riscv64_linux_cva6.shs`

Success markers:

- `OpenSBI` or `Booting Linux`
- `Linux version`
- one of `Freeing unused kernel memory`, `Run /sbin/init`, `BusyBox`, or `login:`

Notes:

- This is the first RV64 local RTL Linux boot reference lane.
- CVA6 requires `RISCV` to point at the compatible RISC-V toolchain.
- Set `CVA6_LINUX_CMD` when a local CVA6 Linux boot command differs from the default smoke-tests entry.
- The repo-native RV64 FPGA shell remains generated separately by `examples/09_embedded/fpga_riscv/generate_linux_rtl.spl`.
