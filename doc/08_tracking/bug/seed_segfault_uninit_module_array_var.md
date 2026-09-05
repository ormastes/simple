# BUG: seed segfaults compiling uninitialized module-level array var (`var x: [T; N]`)

**Status:** RESOLVED (2026-07-11)
**Severity:** medium (crash, and it blocks the natural workaround for the zero-store bloat bug)
**Component:** seed compiler (compiler_rust) — module-level declaration lowering
**Found:** 2026-07-11 (UEFI merged-kernel lane)

## Symptom

Declaring a module-level array variable WITHOUT an initializer, e.g. `var table: [i64; 65536]`, segfaults the Rust seed during compilation (no diagnostic). With `= [0; 65536]` it compiles but triggers the per-element zero-store bloat (`native_build_zero_store_array_init_bloat.md`).

## Fix direction

Uninitialized module-level vars should lower to a plain `.bss` allocation (same as zero-initialized), with a proper diagnostic if the type genuinely requires an initializer. At minimum: never segfault — emit an error.

## Resolution (2026-07-11)

Two coupled defects, both fixed:

1. `src/compiler_rust/type/src/checker_check.rs` — `Node::Let` with no initializer
   never called `bind_pattern`, so the name was unregistered (masking diagnostic
   `undefined identifier` on `compile`/`compile --native`). Now binds the pattern
   and records the annotated type.
2. `src/compiler_rust/compiler/src/hir/lower/module_lowering/module_pass.rs`
   (`record_const_array_init`) — no init was recorded for `expr = None`, so the
   global lowered to a single 8-byte tagged-nil scalar slot: reads returned
   tagged nil (3), writes were lost/corrupted adjacent memory — the segfault
   vector in the SimpleOS kernel build. Now an uninitialized `var name: [T; N]`
   lowers to a zero-filled global identical to `= [0; N]` (kernel code
   legitimately declares uninitialized DMA/table buffers).

Verified: uninit `[i64; 65536]` probe prints `0`/`200` (was `3`/`3`);
`= [0; N]` control unchanged; simple-compiler --lib 2880 passed / 235 failed
(baseline 2878/237 — fixes 2 pre-existing, zero net-new); simple-type --lib 88/0.
