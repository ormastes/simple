# BUG: Module-level val constants are zero in baremetal LLVM targets

**Date:** 2026-05-20
**Status:** FIXED (verified: val→.rodata, const-folded arithmetic, seed rebuilt 2026-05-20)
**Severity:** High (all baremetal kernels affected)
**Component:** LLVM backend codegen

## Problem

Module-level `val` declarations compile to runtime-initialized globals placed in .bss/.data. In baremetal targets, the `_start` entry clears BSS before any runtime initialization runs, so all module-level `val` values read as 0 at runtime.

```
val RAM_BASE: u64 = 0x80000000    # reads as 0 at runtime in baremetal
val HEAP_SIZE: u64 = 8 * 1024 * 1024  # also 0
```

This affects every `.spl` module compiled with `--target riscv64-unknown-none` (and presumably any `*-unknown-none` baremetal target).

## Root cause (two bugs)

**Bug 1: No const-folding for arithmetic.** `module_pass.rs` only recognized `Expr::Integer` literals for `global_init_values`. Expressions like `8 * 1024 * 1024` were not evaluated at compile time, leaving the global zero-initialized.

**Bug 2: All globals hardcoded as mutable.** `lowering_core.rs` passed `is_mutable: true` for every global, so the LLVM backend never marked `val`/`const` as `constant` — they went to `.data` (mutable, zero-init in baremetal) instead of `.rodata`.

## Impact

- **FPGA M-mode kernel**: All module-level constants (RAM_BASE, HEAP_SIZE, register offsets) are zero. Workaround: use function-local `val` with hex literals.
- **uart16550_mmio.spl**: Register offsets (THR=0x00, LSR=0x05, etc.) are zero, causing `uart16550_mmio_write_byte` to infinite-loop reading the wrong register.
- **Any baremetal driver**: Module-level MMIO addresses, bitmask constants, etc. are all zero.

## Fix applied (Option A)

**Bug 1 fix:** Added `try_const_eval()` in `module_pass.rs` — recursive compile-time evaluator for `Integer`, `Binary{Add,Sub,Mul,Div,Mod,BitAnd,BitOr,BitXor,Shl,Shr}`, `Unary{Neg,BitNot}`. Now `8 * 1024 * 1024` folds to `8388608` at HIR lowering.

**Bug 2 fix:** Added `immutable_globals: HashSet<String>` tracking through Lowerer → HirModule → MIR lowering. `val`/`const` declarations populate this set; `lowering_core.rs` reads it to set `is_mutable = false`; LLVM backend emits `set_constant(true)` → `.rodata`.

### Files changed
- `compiler/src/hir/lower/module_lowering/module_pass.rs` — `try_const_eval()` + immutable tracking
- `compiler/src/hir/types/module.rs` — `immutable_globals` field on HirModule
- `compiler/src/hir/lower/lowerer.rs` — `immutable_globals` field on Lowerer
- `compiler/src/mir/lower/lowering_core.rs` — reads `immutable_globals` for `is_mutable` flag

## Current workaround

Use function-local `val` with hex literals:
```
fn boot_main():
    val ram_base: u64 = 0x80000000   # computed from immediate, works
```

## Files affected

- `src/compiler_rust/compiler/src/` — LLVM backend global variable emission
- Every `.spl` file with module-level `val` used in baremetal context
