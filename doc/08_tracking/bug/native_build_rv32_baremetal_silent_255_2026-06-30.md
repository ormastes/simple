# rv32 LLVM native-build broken in this environment (exit 255, no diagnostic)

**Date:** 2026-06-30
**Area:** compiler / native-build (LLVM backend, `riscv32-unknown-none`) — environment/toolchain
**Severity:** blocker (rv32 native-build) + DX (swallowed error)
**Status:** open

## Summary

`bin/simple native-build --backend llvm --target riscv32-unknown-none` exits **255 with no
diagnostic** in this environment — for **both** a new standalone bare-metal entry **and the
proven full-OS rv32 boot entry**. It emits the normal workspace-wide warnings (`export use *`,
deprecated-generics) and the usual non-fatal `[gc-warning] Higher-layer module
'std.nogc_sync_mut.sffi.*' imported in restricted context` lines, then exits 255 — **no
`error:`/`fatal:` line, no panic message, and no intermediate artifact** (`.ll`/`.o`/`.s`) is
written to `build/`. There is no `--verbose`/`--keep-temps`/log flag to surface the real failure.

## Root cause: environmental (verified by baseline)

The decisive test was running the **proven** recipe verbatim:

```sh
SIMPLE_BOOTSTRAP=1 bin/simple native-build --backend llvm --source src/os --source src/lib \
  --entry src/os/kernel/arch/riscv32/boot.spl --entry-closure \
  --linker-script src/os/kernel/arch/riscv32/linker.ld --target riscv32-unknown-none \
  -o build/proven_rv32.elf
# -> PROVEN_BUILD_EXIT=255, no error message, no ELF
```

The proven full-OS entry **also** fails with the same silent 255. So this is **not** entry-specific
— the rv32 LLVM native-build itself is broken/unavailable in this environment. The prebuilt
`build/os/simpleos_riscv32.elf` that *does* boot (verified: `qemu-system-riscv32 ... -bios none`
prints `[BOOT] boot complete`, `PMM OK`, `HEAP OK`, `SVC OK`) is **stale** — produced by an
earlier/different build environment, not reproducible here.

(An earlier draft of this bug wrongly inferred "only the OS entry builds, standalone entries
don't" from the stale prebuilt ELF, without running the baseline. Running the baseline corrected
it: nothing rv32 builds here.)

## What works vs. what doesn't

- ✅ QEMU rv32 boot + serial path (`qemu-system-riscv32`, `riscv64-linux-gnu-gcc` installed; the
  stale prebuilt ELF boots).
- ✅ `bin/simple check` on the firmware rv32 entry (`fw_rv32/entry.spl`).
- ❌ `native-build --backend llvm --target riscv32-unknown-none` — **any** entry, exit 255, no
  diagnostic, no ELF. Self-hosted and seed (`SIMPLE_BOOTSTRAP=1`), ±`src/lib`.

## Two distinct defects

1. **Environmental build break** — the rv32 LLVM native-build produces no ELF here even for the
   proven OS entry. Likely a missing/broken LLVM rv32 target or linker component in this host's
   compiler build (the prebuilt ELF predates the breakage). Fix: restore a working
   `riscv32-unknown-none` LLVM backend/link toolchain, then re-verify the proven recipe builds.
2. **The silent failure (DX)** — native-build emits no diagnostic and no intermediate artifact, so
   the real backend/linker error is invisible. This compounded (1): it took a baseline build to
   even locate the failure. Fix: surface backend/linker stderr; add `--verbose`/`--keep-temps`.

## Impact

Blocks gap-closure **P9** (bare-metal rv32 port of the NVMe firmware) in this environment. The
on-device self-test source is written and `check`-clean (`fw_rv32/entry.spl`, re-expressing the
Lean-proven RAIN reconstruct), but **no rv32 ELF can be built here**, so the boot is **not
observed** and P9 is build-blocked — environmental, not a firmware-logic gap.
