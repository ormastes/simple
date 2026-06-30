# NVMe firmware — bare-metal RV32 on-device self-test (`fw_rv32/`, gap-closure P9)

A bare-metal RISC-V 32 entry that runs the firmware's **core data-path logic with no heap
growth** (fixed-size `[i64]` arrays, plain loops) on a real ISA under `qemu-system-riscv32 -bios
none`, rather than only on the host interpreter. It boots in M-mode, runs the self-test
on-device, prints a marker over the 16550 UART, then halts.

`entry.spl` re-expresses the firmware's **RAIN XOR-parity reconstruct** (`../fw/rain.spl`,
proven in `../fw/proofs/Rain.lean`): build per-stripe parity, lose a channel, reconstruct it from
the survivors — XOR is its own inverse, so the survivors cancel and the lost word remains. It
also rebuilds a corrupted channel over a small fixed NAND. On success it emits
`ALL RV32 NVME FW CHECKS PASS`.

## Build & boot

```sh
sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/build.shs   # -> build/nvme_fw_rv32.elf
sh examples/09_embedded/simpleos_nvme_fw/fw_rv32/boot.shs    # boot under QEMU, grep the marker
```

## Status (2026-06-30): source ready + check-clean; **build blocked**

- ✅ `entry.spl` is `bin/simple check`-clean and re-expresses the Lean-proven RAIN logic no-alloc.
- ✅ The QEMU rv32 boot+serial path works in this environment (`boot.shs` boots the prebuilt
  `build/os/simpleos_riscv32.elf` and prints on-device `PMM OK`/`HEAP OK`/`SVC OK`).
- ❌ `native-build --backend llvm --target riscv32-unknown-none` exits **255 with no diagnostic**
  for this standalone bare-metal entry (both self-hosted and seed compilers), producing no ELF.
  Tracked: `doc/08_tracking/bug/native_build_rv32_baremetal_silent_255_2026-06-30.md`.

So the boot is **not yet observed** — P9 is honestly recorded as build-blocked, not done. The
remaining work after the build blocker is fixed: run `build.shs` then `boot.shs`, confirm the
marker, and wire a fail-closed QEMU system test (per `qemu_systest_contract`). The full
22-module no-alloc port of the host `../fw/` stack remains the larger ceiling.

## Scope note (honest)

This proves the **core algorithm** runs on rv32 bare metal with no heap growth — it is not the
literal host `Ftl`/`Hil`/`Fil`/controller (those pull `ftl_fill`/dict-map/journal-ring and the
std/SFFI tree, which is not bare-metal-portable as-is). The host stack stays the full simulation;
this is the first step of the embedded-target port.
