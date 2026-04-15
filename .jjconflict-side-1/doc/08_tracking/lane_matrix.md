# Remote Execution Lane Matrix

**Generated:** 2026-04-04  
**Source of truth:** `src/lib/nogc_sync_mut/debug/remote/exec/lane_registry.spl`  
**Status:** Active

## Lane Status

| Lane ID | Arch | Adapter | Proof | Status | Authoritative | Primary Channel | Fallback Channel | Authoritative Spec |
|---------|------|---------|-------|--------|--------------|-----------------|------------------|--------------------|
| qemu_rv32_semihost | riscv32 | qemu_gdb | compiled | **stable** | yes | semihost_text | exit_code | `test/integration/remote_jit/qemu_rv32_library_semihost_spec.spl` |
| qemu_arm_semihost | arm32 | qemu_gdb | compiled | **stable** | yes | semihost_text | exit_code | `test/integration/remote_jit/qemu_arm_composite_runner_spec.spl` |
| x86_64_direct_boot | x86_64 | direct_boot | compiled | **stable** | yes | exit_code | — | `test/qemu/os/boot/x86_64_boot_qemu_spec.spl` |
| ch32v307_wlink | riscv32 | wlink_cli | compiled | **host_aware** | yes | register_readback | ram_sentinel | `test/integration/remote_jit/ch32v307_composite_runner_spec.spl` |
| stm32h7_openocd | arm32 | openocd_gdb | compiled | **host_aware** | yes | register_readback | ram_sentinel | `test/integration/remote_jit/stm32h7_composite_runner_spec.spl` |
| stm32h7_trace32 | arm32 | trace32 | compiled | **host_aware** | yes | debugger_console | register_readback | `test/system/t32_terminal_power_remote_spec.spl` |
| ghdl_rv32_semihost | riscv32 | ghdl_sim | compiled | **host_aware** | yes | semihost_text | exit_code | `test/feature/baremetal/ghdl_riscv32_semihost_spec.spl` |
| ghdl_rv32_mailbox | riscv32 | ghdl_sim | compiled | **host_aware** | yes | ram_sentinel | register_readback | `test/feature/baremetal/ghdl_riscv32_mailbox_spec.spl` |
| fpga_jtag_zedboard | arm32 | openocd_gdb | structural | **in_progress** | no | register_readback | — | *(none — quarantined)* |
| rv32_raw_injected | riscv32 | qemu_gdb | structural | transport_only | no | register_readback | — | `test/integration/remote_jit/qemu_rv32_raw_injected_regression_spec.spl` |
| baremetal_runtime_check | riscv32 | qemu_gdb | interpreter | transport_only | no | exit_code | — | `test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl` |

## Classification Summary

- **Authoritative (8):** Stable + host-aware lanes
- **Stable (3):** QEMU RV32 semihost, QEMU ARM semihost, x86_64 direct boot
- **Host-aware (5):** CH32V307 via wlink, STM32H7 via OpenOCD, STM32H7 via TRACE32, GHDL RV32 semihost, GHDL RV32 mailbox
- **Transport-only (2):** RV32 raw injected regression, baremetal runtime check
- **In-progress (1):** ZedBoard/FPGA JTAG

## Lane Definitions

### Stable Lanes

Stable lanes run without physical hardware in CI or controlled environments:

- **qemu_rv32_semihost**: QEMU RISC-V 32 virt machine with semihosting. Primary evidence lane for RV32 compiled execution.
- **qemu_arm_semihost**: QEMU ARM virt machine with semihosting. Primary evidence lane for ARM compiled execution.
- **x86_64_direct_boot**: Direct x86_64 baremetal boot via QEMU or native. Primary evidence lane for x86_64 boot.

### Host-Aware Lanes

Lanes that skip cleanly when prerequisites are missing:

- **ch32v307_wlink**: CH32V307 RISC-V MCU via WCH-Link USB probe. Requires `wlink` CLI and physical board.
- **stm32h7_openocd**: STM32H7 Cortex-M7 via OpenOCD + ST-Link. Requires `openocd`, `gdb`, and physical board.
- **stm32h7_trace32**: STM32H7 Cortex-M7 via Lauterbach TRACE32. Requires T32 installation and license.
- **ghdl_rv32_semihost**: GHDL VHDL simulation of RV32 with semihosting. Requires `ghdl`, `clang`, `ld.lld`, `llvm-objcopy`. Implemented with bounded scope — semihost/GDB-backed execution is validated.
- **ghdl_rv32_mailbox**: GHDL VHDL simulation of RV32 with MMIO mailbox transport. Requires same toolchain as semihost. Debugger-independent — uses memory-mapped registers at 0x80FF0000 instead of ARM semihosting traps, with ram_sentinel at 0x80008000 for result collection.

### Transport-Only Lanes

Verify debugger plumbing, not authoritative workload execution:

- **rv32_raw_injected**: Raw code injection via QEMU GDB for regression testing.
- **baremetal_runtime_check**: Runtime environment validation (composite parsing, tool discovery).

### In-Progress Lanes

Not yet promoted to supported status:

- **fpga_jtag_zedboard**: ZedBoard Zynq-7020 FPGA via JTAG. **Quarantined** — no authoritative compiled execution proof exists. Will remain in-progress until JTAG chain + upload/run/result proof is established, or will be explicitly excluded.

## Capability Detection

All lanes use centralized capability probes from `capability_report.spl`:

| Status | Meaning |
|--------|---------|
| `ready` | All prerequisites met, lane can execute |
| `skip_missing_tool` | Required CLI tool not installed |
| `skip_missing_board` | Tool present but target hardware not detected |
| `blocked_permissions` | Tool and board present but access denied |
| `blocked_host_config` | Host configuration prevents execution |
| `failed_runtime` | Execution attempted but failed (regression) |

## Result Channels

All lanes produce canonical `ResultPacket` objects:

| Channel | Used By | Description |
|---------|---------|-------------|
| semihost_text | QEMU, GHDL | ARM/RISC-V semihosting output capture |
| exit_code | x86_64, runtime check | Process exit code |
| register_readback | CH32, STM32, FPGA, raw injected | Read return register after halt |
| ram_sentinel | CH32 (fallback), STM32 (fallback), GHDL mailbox (primary) | Read known RAM address for result |
| debugger_console | TRACE32 | Parse debugger output for result |

## Recommended Public Classification

After completion of all phases:

- **Stable reference lanes:** QEMU RV32, QEMU ARM, x86_64 baremetal
- **Host-aware supported:** CH32V307, STM32H7/OpenOCD, STM32H7/TRACE32
- **Host-aware simulation:** GHDL RV32 semihost (semihosting-backed), GHDL RV32 mailbox (MMIO-backed, debugger-independent)
- **Excluded:** ZedBoard/FPGA (quarantined until real execution proof)

## SYS-GUI-008 virtio-gpu Lane (2026-04-15)

**Status: Round-3 in progress — waiting on boot verification (not yet green)**

- DECODE_INT ram_write bug fixed (commit `3ab3ffeee9dd`, 2026-04-15)
- PPM diff harness spec implemented (3-B done)
- sys-gui-006 framebuffer baseline LIVE-GREEN (diff reference available)
- Remaining before green: boot verification, baseline PPM capture (3-A/3-C), final doc update (3-D)
- Tracked by: `doc/08_tracking/todo/sys_gui_008_virtio_gpu_qemu.md`
