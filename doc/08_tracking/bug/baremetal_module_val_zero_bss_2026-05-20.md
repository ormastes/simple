# BUG: Module-level val constants are zero in baremetal LLVM targets

**Date:** 2026-05-20
**Status:** OPEN
**Severity:** High (all baremetal kernels affected)
**Component:** LLVM backend codegen

## Problem

Module-level `val` declarations compile to runtime-initialized globals placed in .bss/.data. In baremetal targets, the `_start` entry clears BSS before any runtime initialization runs, so all module-level `val` values read as 0 at runtime.

```
val RAM_BASE: u64 = 0x80000000    # reads as 0 at runtime in baremetal
val HEAP_SIZE: u64 = 8 * 1024 * 1024  # also 0
```

This affects every `.spl` module compiled with `--target riscv64-unknown-none` (and presumably any `*-unknown-none` baremetal target).

## Root cause

The Simple compiler's LLVM backend emits module-level `val` as:
1. A global variable in .bss (zero-initialized)
2. A static constructor function that stores the computed value

Baremetal targets have no `.init_array` / `__libc_start_main` mechanism to run static constructors. The `_start` assembly clears BSS, then jumps to the kernel main — constructors never execute.

## Impact

- **FPGA M-mode kernel**: All module-level constants (RAM_BASE, HEAP_SIZE, register offsets) are zero. Workaround: use function-local `val` with hex literals.
- **uart16550_mmio.spl**: Register offsets (THR=0x00, LSR=0x05, etc.) are zero, causing `uart16550_mmio_write_byte` to infinite-loop reading the wrong register.
- **Any baremetal driver**: Module-level MMIO addresses, bitmask constants, etc. are all zero.

## Proposed fix

For `val` declarations whose initializers are compile-time constant expressions (literals, arithmetic on literals, shifts, bitwise ops):

**Option A (recommended):** Emit as LLVM `constant` in `.rodata` instead of a global with constructor:
```llvm
@RAM_BASE = internal constant i64 2147483648  ; 0x80000000 — in .rodata, survives BSS clear
```

**Option B:** Emit a `.init_array` entry AND have the baremetal `_start` template call `__init_array_start..end` after BSS clearing but before kernel main.

**Option C (partial):** Document that module-level `val` is unsupported in baremetal and lint against it. Least work, most friction.

Option A is cleanest — purely compile-time constants should never need runtime initialization.

## Current workaround

Use function-local `val` with hex literals:
```
fn boot_main():
    val ram_base: u64 = 0x80000000   # computed from immediate, works
```

## Files affected

- `src/compiler_rust/compiler/src/` — LLVM backend global variable emission
- Every `.spl` file with module-level `val` used in baremetal context
