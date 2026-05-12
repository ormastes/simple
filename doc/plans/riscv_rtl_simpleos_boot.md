# RISC-V RTL + SimpleOS Boot Plan

**Date:** 2026-05-11 (updated 2026-05-12)

## Goal

Production-level RISC-V system:
1. CPU RTL written in Simple (.spl) → VHDL via compiler backend
2. Three deployment layers: GHDL simulation → QEMU virt → Kria K26 FPGA
3. SimpleOS boots with HTTP + TLS + auth/RBAC server stack

## Track A: RTL CPU + SoC — Status

| Phase | Description | Status |
|-------|-------------|--------|
| A1 | RV32I core in .spl RTL | DONE |
| A2 | M-mode CSR + trap handling | DONE (in SoC gen) |
| A3 | SoC peripherals (UART, CLINT, bootrom) | DONE |
| A4 | Wishbone bus + SoC top + testbench | DONE (`af7af19`) |
| A5 | PLIC + interrupt routing | Not started |
| A6 | MMU (Sv32/Sv39) | Not started |
| A7 | RV64 widening + K26 FPGA | Not started |
| A8 | Ethernet MAC | Not started |

**A1-A4 proven:** GHDL simulation runs 49 cycles, outputs "SimpleOS\n", halts.

## Track B: SimpleOS QEMU Boot — Status

| Phase | Description | Status |
|-------|-------------|--------|
| B1 | Boot wiring + cross-compilation | IN PROGRESS |
| B2 | TCP shim (stubs exist) | Not started |
| B3 | IoDriver shim (hardest) | Not started |
| B4 | TLS on baremetal | Not started |
| B5 | HTTP server launch | Not started |
| B6 | QEMU integration tests | Not started |

### B1 Detail — Current Blockers

**Done:**
- Runtime FFI fix: all `rt_*` declared for all targets (was excluding Sys/Async)
- `os_main.spl`: removed broken `boot_fs` dependency
- `width_index.spl`: `me` → `self` parse fix for `--entry-closure` discovery
- Identified correct build flags: `--entry-closure` + `--linker-script`

**Remaining (2 files):**

1. `src/lib/nogc_async_mut/http_server/compression.spl`
   - Error: "Cannot infer field type: struct 'ANY' field 'zstd'"
   - Likely: `CompressionCodec.zstd` enum variant not resolving

2. `src/lib/nogc_async_mut/http_server/worker.spl`
   - Error: "Cannot infer field type: struct 'ANY' field 'flags'"
   - Likely: `completion.flags` on untyped IoDriver completion struct

**After fixing those:** expect linker issues with unresolved `rt_*` externs needing baremetal stubs.

### Build Command

```bash
SIMPLE_BOOTSTRAP=1 src/compiler_rust/target/bootstrap/simple native-build \
  --source src/os --source src/lib \
  --entry src/os/kernel/arch/riscv64/boot.spl \
  --entry-closure \
  --linker-script src/os/kernel/arch/riscv64/linker.ld \
  --target riscv64gc-unknown-none \
  -o build/simpleos-rv64.elf
```

## Key Files

| File | Role |
|------|------|
| `src/os/kernel/arch/riscv64/boot.spl` | Entry: `_start → boot_main` |
| `src/os/kernel/boot/riscv_boot_mem.spl` | PMM + heap init |
| `src/os/kernel/boot/os_main.spl` | Service init → HTTP server |
| `src/os/kernel/arch/riscv64/linker.ld` | Linker script (0x80200000) |
| `src/lib/nogc_async_mut/http_server/` | Async HTTP server (21 files) |
| `src/os/kernel/net/http_baremetal.spl` | Baremetal HTTP launcher |
| `src/os/kernel/net/{tcp,driver,thread}_shim.spl` | Baremetal shim stubs |
| `src/lib/hardware/fpga_linux/soc_vhdl_gen.spl` | SoC VHDL generator |
| `src/compiler_rust/compiler/src/codegen/runtime_ffi.rs` | Runtime FFI declarations |
| `scripts/qemu_rv64_http_test.shs` | QEMU integration test script |

## Convergence (C1)

Requires Track A phase A7 + Track B phase B6 both complete.
Load SimpleOS ELF into K26 FPGA SoC RAM, HTTP server on real hardware.
