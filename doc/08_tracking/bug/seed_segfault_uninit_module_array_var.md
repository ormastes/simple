# BUG: seed segfaults compiling uninitialized module-level array var (`var x: [T; N]`)

**Status:** open
**Severity:** medium (crash, and it blocks the natural workaround for the zero-store bloat bug)
**Component:** seed compiler (compiler_rust) — module-level declaration lowering
**Found:** 2026-07-11 (UEFI merged-kernel lane)

## Symptom

Declaring a module-level array variable WITHOUT an initializer, e.g. `var table: [i64; 65536]`, segfaults the Rust seed during compilation (no diagnostic). With `= [0; 65536]` it compiles but triggers the per-element zero-store bloat (`native_build_zero_store_array_init_bloat.md`).

## Fix direction

Uninitialized module-level vars should lower to a plain `.bss` allocation (same as zero-initialized), with a proper diagnostic if the type genuinely requires an initializer. At minimum: never segfault — emit an error.
