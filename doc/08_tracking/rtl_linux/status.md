# RISC-V Local RTL Linux Status

Current target: local RTL simulation boots Linux for both RV32 and RV64 before FPGA hardware arrives.

## Lanes

| Lane | Backend | Runner | Status Meaning |
|------|---------|--------|----------------|
| RV32 | `litex-vexriscv-verilator` | `scripts/rtl_riscv32_linux_litex.shs` | PASS only when local Verilator simulation reaches Linux/userspace serial markers. |
| RV64 | `cva6-verilator` | `scripts/rtl_riscv64_linux_cva6.shs` | PASS only when local Verilator simulation reaches firmware, Linux, and userspace serial markers. |

## Boundaries

- QEMU RISC-V boot scripts remain functional references, not RTL success evidence.
- GHDL RV32 remains a baremetal RTL lane, not Linux boot evidence.
- Generated Simple FPGA RTL shells are valid VHDL/elaboratable outputs, not Linux-capable SoCs until CPU/MMU/peripheral wiring exists.

## Commands

Tool probe:

```sh
sh scripts/check-riscv-rtl-linux-smoke.shs --check-tools
```

Run both lanes:

```sh
sh scripts/check-riscv-rtl-linux-smoke.shs
```

Run one lane:

```sh
sh scripts/check-riscv-rtl-linux-smoke.shs --rv32-only
sh scripts/check-riscv-rtl-linux-smoke.shs --rv64-only
```
