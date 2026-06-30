# NVMe firmware — bare-metal RV32 on-device self-test (`fw_rv32/`, gap-closure P9)

`entry.spl` is an **array-free, scalar** re-expression of the firmware's core **RAIN XOR-parity
reconstruct** (`../fw/rain.spl`, proven in `../fw/proofs/Rain.lean`), written to run inside the
bare-metal rv32 boot path with **no heap and no arrays** — matching the constraint documented in
`src/os/kernel/arch/riscv32/boot.spl` ("keep this module freestanding and minimal ... without
pulling runtime formatting, arrays, or boot metadata into the first-stage entry object"). It
verifies, with eight scalar channels, that parity XOR the survivors recovers any lost channel
exactly (XOR is its own inverse), plus a channel-failure rebuild, then prints
`ALL RV32 NVME FW CHECKS PASS` over the UART via `rt_riscv_uart_put` — one byte at a time, exactly
like `boot.spl`'s `_line_*` helpers.

The scalar logic is `bin/simple check`-clean and host-verified (the XOR-cancel math reproduces
`fail=0`).

## Integration (when the rv32 toolchain is restored)

`entry.spl` exposes `nvme_fw_rv32_selftest()`, designed to be called from the rv32 boot chain:

1. Add a `nvme_fw_rv32_selftest()` call in `src/os/kernel/arch/riscv32/boot.spl` `boot_main`,
   after `riscv_noalloc_log_init()`.
2. Build the rv32 OS ELF: `sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs`.
3. Boot + check the marker: `sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/boot.shs <elf>`.

(No standalone `@naked _start` is hand-written here — the proven `_start`/crt/UART live in
`boot.spl`; reusing them is more reliable than an untestable hand-rolled entry.)

## Status (2026-06-30): toolchain bug FIXED; boot blocked on the bare-metal rv32 runtime

- ✅ `entry.spl` is `check`-clean, array-free, and the RAIN logic is host-verified (XOR-cancel
  reproduces `fail=0`).
- ✅ **Toolchain bug fixed.** `native-build --target riscv32-unknown-none` no longer exits with a
  silent 255: it now routes to the in-process Rust LLVM handler, **compiles this entry to riscv
  objects**, and links with real, actionable errors (commits `a0652371728` pure-Simple
  surfacing + `187c62110138` Rust cross-target routing).
- ❌ **Boot not yet observed** — the freestanding rv32 link is missing runtime primitives:
  `rt_native_eq`/`rt_native_neq` (emitted for `==`/`!=`), `rt_riscv_uart_put` (the C stub is
  riscv64-only), plus a rooted bare-metal `_start` (the linker GCs all code without one).
  **Verified** these are *not* resolved by `--release` or `--runtime-bundle` — a genuine
  bare-metal rv32 **runtime** gap, not a toolchain/opt/config issue. Tracked:
  `doc/08_tracking/bug/native_build_rv32_baremetal_silent_255_2026-06-30.md`.
- ⚠️ The Rust routing fix is **committed as source** and verified via a freshly-built binary, but
  is **not yet live in the shared `bin/simple`** (needs a rebuild + deploy of the self-hosted
  binary). The pure-Simple timeout-surfacing fix *is* live (interpreted).

P9 is honestly recorded as **toolchain-fixed, boot-blocked on the freestanding rv32 runtime** —
not done. Completing that runtime (the missing `rt_*` + a bare-metal `_start`/entry) is the next
step; the full 22-module no-alloc port of `../fw/` remains the larger ceiling.
