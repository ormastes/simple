# native-build rv32 bare-metal standalone entry fails silently (exit 255, no diagnostic)

**Date:** 2026-06-30
**Area:** compiler / native-build (LLVM backend, `riscv32-unknown-none`)
**Severity:** blocker (for standalone bare-metal rv32 entries) + DX (swallowed error)
**Status:** open

## Summary

`bin/simple native-build --backend llvm --target riscv32-unknown-none` exits **255 with no
diagnostic** when the `--entry` is a small standalone bare-metal program (a `fn _start()` that
uses only `os.kernel.boot.mmio` + fixed `[i64]` arrays + loops). It emits the normal
workspace-wide warnings (`export use *`, deprecated-generics) and the usual non-fatal
`[gc-warning] Higher-layer module 'std.nogc_sync_mut.sffi.*' imported in restricted context`
lines, then exits 255 — **no `error:`/`fatal:` line, no panic message, and no intermediate
artifact** (`.ll`/`.o`/`.s`) is written to `build/`. There is no `--verbose`/`--keep-temps`/log
flag to surface the real failure.

## Repro

Entry (check-clean — `bin/simple check` reports "All checks passed"):
`examples/09_embedded/simpleos_nvme_fw/fw_rv32/entry.spl`

```sh
SIMPLE_BOOTSTRAP=1 bin/simple native-build --backend llvm \
  --source src/os --source src/lib \
  --source examples/09_embedded/simpleos_nvme_fw/fw_rv32 \
  --entry examples/09_embedded/simpleos_nvme_fw/fw_rv32/entry.spl --entry-closure \
  --linker-script src/os/kernel/arch/riscv32/linker.ld \
  --target riscv32-unknown-none \
  -o build/nvme_fw_rv32.elf
# -> exit 255, no error message, build/nvme_fw_rv32.elf not produced
```

Tried, all identical (255, silent): self-hosted `bin/simple` and seed (`SIMPLE_BOOTSTRAP=1`);
with and without `--source src/lib`.

## What works (so it is build-side, not env/runtime)

- `qemu-system-riscv32 -machine virt -cpu rv32 -bios none -kernel build/os/simpleos_riscv32.elf`
  boots the **prebuilt** rv32 OS ELF here and prints on-device self-tests over serial
  (`[BOOT] boot complete`, `PMM OK`, `HEAP OK`, `SVC OK`). The QEMU rv32 boot + serial path is
  fine in this environment; `qemu-system-riscv32` and `riscv64-linux-gnu-gcc` are installed.
- The entry compiles clean under `bin/simple check`.

## Two distinct defects

1. **The silent failure** — native-build produces no diagnostic and no intermediate artifact, so
   the actual rv32 codegen/link error cannot be seen. This alone blocks diagnosis and should be
   fixed first (surface the backend/linker stderr; add `--verbose`/`--keep-temps`).
2. **The standalone bare-metal entry not building** — the full-OS entry
   (`src/os/kernel/arch/riscv32/boot.spl`) is the only rv32 entry known to produce a bootable
   ELF; a minimal standalone `fn _start()` entry does not. Whether this is the gc-family
   restriction being treated as fatal for the restricted target, a missing crt/_start wiring for
   non-OS entries, or an array-codegen gap is unknown until defect (1) is fixed.

## Impact

Blocks gap-closure **P9** (bare-metal rv32 no-alloc port of the NVMe firmware). The on-device
self-test source is written and `check`-clean (`fw_rv32/entry.spl`, re-expressing the
Lean-proven RAIN reconstruct on fixed arrays); it cannot be built into an ELF here, so the boot
is **not observed** and P9 is recorded as build-blocked — not done.
