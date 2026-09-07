# `simple-runtime` cdylib fails with 23 `rt_simd_*` duplicate-symbol errors

- Filed: 2026-09-07 (regression introduced by PR #493, branch
  `work/stage2-simd-iofile`, commit `f66280e066534701161eb5b67e808554805c1a71`)
- Status: **RESOLVED** same day.

## Symptom

PR #493 added C implementations of the `rt_simd_*` family to
`src/runtime/runtime_simd_dispatch.c` to close 23 of the 109 remaining
Stage-2 core-C-bootstrap undefined symbols (verified there by relink,
214 -> 178 undefined). That fix works for its stated purpose, but it breaks
the `simple-runtime` cdylib target: building with `--features
runtime-symbol-table` (which the `simple-compiler`, `simple-native-all`, and
`simple-driver` crates all request unconditionally in their `Cargo.toml`,
so any full-workspace/binary build unifies this feature in) turns on
`build.rs`'s `+whole-archive=runtime_sffi_c` linkage, forcing every object in
the C archive — including the newly-added `runtime_simd_dispatch.c` block —
into the same link as the pre-existing Rust `#[no_mangle] pub extern "C" fn
rt_simd_*` exports in `simd_int_ops.rs` (16), `simd_byte_ops.rs` (2),
`simd_aes_ops.rs` (2), and `simd_clmul_ops.rs` (3) = 23 names, all of which
now collide.

**Note on reproduction:** a plain `cargo build --release -p simple-runtime`
(default features only) does NOT reproduce this — whole-archive is gated
behind `CARGO_FEATURE_RUNTIME_SYMBOL_TABLE`, and without it the linker's
ordinary lazy archive extraction never needs to pull in
`runtime_simd_dispatch.o` (nothing else in a default build references those
symbols). Reproduce with:

```
cd src/compiler_rust && CARGO_TARGET_DIR=<dir> cargo build --release \
  -p simple-runtime --features runtime-symbol-table -j4
```

which fails with 23 `mold: error: duplicate symbol: ... rt_simd_NAME`
entries (one per name), confirmed both before and after the fix below.

`cargo check` never catches this (link-time only, `check` doesn't link).

## Root-cause classification (not uniform across the 23)

A predecessor investigation established, by disassembling real call sites in
the kept failed-link object set (`mod_842.o` for i32x4/i32x8, `mod_843.o`
for u8x16/u64x2), that real compiled calls pass a tagged-pointer flat-struct
arg (matching `runtime_simd_dispatch.c`'s pre-existing `rt_simd_add_f32x4`-
style convention), not the Rust side's scalar-lane-array ABI. This session
extended that investigation to all 23 names and found they split into two
groups:

**Group A — 21 names, Rust side dead and wrong-ABI, C side correct → deleted
the Rust `#[no_mangle]` wrappers.** All of:
- `rt_simd_{add,sub,mul,xor,and,or,shl,shr}_i32x4` and `..._i32x8` (16,
  `simd_int_ops.rs`)
- `rt_simd_{add,xor}_u8x16` (2, `simd_byte_ops.rs`)
- `rt_simd_clmul_{lo,hi}_u64`, `rt_simd_xor_u64x2` (3, `simd_clmul_ops.rs`)

None of these 21 are in `codegen::runtime_sffi::RUNTIME_FUNCS` (the
codegen call-signature table), none are called by the interpreter (which
dispatches through `compiler/src/interpreter_extern/simd.rs` straight to the
private lane-kernel functions, e.g. `add_i32x4`, bypassing the `extern "C"`
wrapper entirely), and their signatures do not match the corresponding
`extern fn` declarations in `src/lib/nogc_sync_mut/simd.spl` /
`simd_crypto.spl` (which take `Vec4i`/`Vec8i`/`Vec16u8`/`Vec2u64` struct
params — i.e. the tagged-pointer convention — not 8+ scalar args). The Rust
`simd_int_ops.rs` file's own comment already admitted this: "once a Vec4i
marshalling layer lands they will receive the actual lane data" — it never
landed, and nothing ever called these wrappers. Deleting them is a
dead/wrong-code removal, not a behavior change for any reachable caller.
Their private lane-kernel functions (`add_i32x4`, `clmul_lo_u64`, etc.) are
untouched and still used directly by the interpreter path. Two
`simd_int_ops.rs` unit tests that exercised the now-deleted `_i32x8` raw
`*const i32` wrappers' misaligned-pointer handling were removed with them
(the misalignment concern was specific to their now-gone FFI marshalling).

**Group B — 2 names, Rust side correct and actively used → kept both sides,
weak-linked the C definitions.** `rt_simd_aes_round_u8x16` and
`rt_simd_aes_round_last_u8x16` (`simd_aes_ops.rs`) take `RuntimeValue`
params matching the tagged-pointer convention, ARE registered in
`RUNTIME_FUNCS` (`codegen/runtime_sffi.rs:594-595`, `&[I64,I64]->&[I64]`),
and ARE exercised by a real unit test
(`flat_struct_wrapper_fips197_round1`) that validates the exact
`rt_alloc`-based flat-struct memory layout Cranelift codegen produces.
Deleting the Rust side here would have silently swapped a verified,
registered, currently-reachable implementation for a newly-added one on any
Rust-linked target (cdylib / native-all / driver) — which the task's
constraint ("nothing silently changes which implementation compiled code
reaches") rules out. Resolved instead by marking the two C definitions in
`runtime_simd_dispatch.c` `__attribute__((weak))` on GNU/Clang non-Windows
targets (mirroring the **exact existing precedent** in
`runtime_memtrack.c` for `rt_heap_live_bytes`/`rt_heap_peak_bytes` vs
`value::heap`), gated by a new `SIMPLE_RUNTIME_RUST_PROVIDES_AES_ROUND_U8X16`
macro that `build.rs` defines only on Windows (MSVC has no weak attribute;
Windows-GNU drops a weak COFF alias under `--gc-sections`, so both Windows
ABIs need the C side suppressed outright there, same as the heap-counters
precedent). On every other platform, ELF strong-beats-weak resolution means:
a link that also carries the Rust runtime keeps the Rust definition; the
standalone core-C-bootstrap Stage2 link (which never links the Rust runtime)
keeps the C definition as the sole provider, unaffected by weak vs strong.

## Fix

- `src/compiler_rust/runtime/src/value/simd_int_ops.rs` — removed the 16
  `#[no_mangle] pub extern "C" fn rt_simd_*_i32x{4,8}` wrappers and the two
  unit tests that exercised their raw-pointer FFI marshalling.
- `src/compiler_rust/runtime/src/value/simd_byte_ops.rs` — removed the 2
  `rt_simd_{add,xor}_u8x16` wrappers.
- `src/compiler_rust/runtime/src/value/simd_clmul_ops.rs` — removed the 3
  `rt_simd_{clmul_lo,clmul_hi}_u64`/`rt_simd_xor_u64x2` wrappers.
- `src/compiler_rust/runtime/src/value/mod.rs` — updated the `pub use`
  re-export blocks to match (kept the aes_round re-export unchanged).
- `src/runtime/runtime_simd_dispatch.c` — wrapped `rt_simd_aes_round_u8x16`/
  `rt_simd_aes_round_last_u8x16` in the weak/suppress conditional described
  above (Group B); the other 21 C definitions are unchanged.
- `src/compiler_rust/runtime/build.rs` — defines
  `SIMPLE_RUNTIME_RUST_PROVIDES_AES_ROUND_U8X16` alongside the existing
  `SIMPLE_RUNTIME_RUST_PROVIDES_HEAP_COUNTERS` Windows gate.

## Verification

1. **cdylib builds** (the check that failed before the fix):
   `cargo build --release -p simple-runtime --features runtime-symbol-table
   -j4` → `Finished \`release\` profile [optimized] target(s) in 34.03s`, 0
   errors, 0 duplicate-symbol diagnostics (previously 23). Re-confirmed the
   failure reproduces pre-fix (same command on the merged-but-unfixed tree):
   23 `mold: error: duplicate symbol` lines, one per name in the list above.
2. `cargo check --release --bin simple -j4` → clean, 0 errors (7 pre-existing
   unrelated warnings only).
3. **Relink of the kept Stage2 object set**, methodology: copied the
   read-only `native-objects-8HIZif` directory (1778 kept `.o` files, the
   real failed-link artifacts this PR was written against) to a scratch dir;
   separately compiled `src/runtime/*.c`'s core-C-bootstrap file list (the
   same 26 files / flags `build_c_runtime_library` in
   `native_project/tools.rs` uses, `-DSIMPLE_CORE_C_STANDALONE=1
   -DSIMPLE_RUNTIME_MEMORY_OWNER=1`, no
   `SIMPLE_RUNTIME_RUST_PROVIDES_AES_ROUND_U8X16` — i.e. the exact flags
   Stage2 itself uses, which do NOT define the new suppression macro, so the
   weak-GNU branch is taken and all 23 names are still defined, 21 strong
   (`T`) unchanged + 2 now weak (`W`) but present) into a fresh archive; then
   ran `clang -shared -fuse-ld=lld -Wl,--error-limit=0 -Wl,--no-undefined`
   over the 1778 objects alone (baseline: 670 undefined symbols, of which 62
   are `rt_simd_*`, all 23 target names among them) and again with the fresh
   archive added (78 undefined symbols remain, **0 of them `rt_simd_*`** —
   all 23 resolved, no regression on the other ~39 non-colliding `rt_simd_*`
   names either). The 78 residual undefined symbols are pre-existing/expected
   (libm functions not linked in this minimal proxy, Simple-compiler-level
   method symbols needing archives outside this scope, and the PR's own
   documented "54-symbol remainder still deferred" set, e.g.
   `rt_exec`/`rt_file_atomic_write_mode`/`rt_file_list_dir`) — none are new
   regressions introduced by this fix. This is a direct-`ld` proxy for the
   full `bin/simple native-build --runtime-bundle core-c-bootstrap` pipeline
   (not re-run here per task scope: no full bootstrap, no `bin/simple`
   writes), using the identical C source list, compile flags, and the real
   kept object set — not a full resolving link (the real pipeline also needs
   `libsimple_native_all.a`/`libsimple_compiler_backfill.a`/libm/etc., which
   this proxy does not link).
4. `sh scripts/check/check-c-runtime-compiles-push.shs` →
   `PASS — 137 file(s) compiled, 0 errors (5 skipped for unavailable
   external dependencies)` (skips are pre-existing external-SDK headers,
   unrelated to this change).
5. `cargo test -p simple-runtime --lib value::simd -- --test-threads=4` →
   `test result: ok. 51 passed; 0 failed`, including
   `simd_aes_ops::tests::flat_struct_wrapper_fips197_round1` (proves the
   kept Rust aes_round wrapper + its flat-struct layout test still pass).

## Residual risk

- The weak-symbol resolution for Group B has not been independently
  re-verified against `mold` specifically (only `ld.lld`, per the CI/link
  toolchain used in this session) — ELF strong-over-weak precedence is a
  platform-standard behavior, not a linker-specific quirk, but this was not
  separately re-measured with mold.
- Not verified: whether `simple-native-all`/`simple-driver`
  (`cargo build`, not `check`) also hit this exact collision independently
  of the cdylib target — both crates request `runtime-symbol-table` too,
  so plausibly yes, but building those binaries end-to-end was out of this
  task's scope (no full bootstrap).
