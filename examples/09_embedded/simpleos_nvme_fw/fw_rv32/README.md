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

## Status (2026-06-30): source ready + check-clean; **build environmentally blocked**

- ✅ `entry.spl` is `check`-clean, array-free, and follows `boot.spl`'s proven UART pattern; the
  RAIN logic is host-verified.
- ✅ The QEMU rv32 boot+serial path works here (`boot.shs` boots the **prebuilt**
  `build/os/simpleos_riscv32.elf` and prints on-device `PMM OK`/`HEAP OK`/`SVC OK`).
- ❌ `native-build --backend llvm --target riscv32-unknown-none` exits **255 with no diagnostic**
  in this environment — **including the proven full-OS recipe** (verified by running it), not just
  this entry. So no rv32 ELF can be built here and the boot is **not observed**. The prebuilt ELF
  that boots is stale (from an earlier build environment). Tracked:
  `doc/08_tracking/bug/native_build_rv32_baremetal_silent_255_2026-06-30.md`.

P9 is honestly recorded as **build-blocked (environmental)**, not done — it is not a
firmware-logic gap. The full 22-module no-alloc port of the host `../fw/` stack remains the larger
ceiling beyond this self-test slice.
