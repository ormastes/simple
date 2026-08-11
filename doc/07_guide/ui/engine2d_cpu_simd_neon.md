# Engine2D CPU SIMD — genuine AVX2/NEON row kernels

The CPU ("software") engine2d backend's hot pixel-row kernels are backed by
real SIMD instructions, not scalar loops that merely *report* `has_neon`. On
aarch64 the fill and copy spans execute NEON; on x86_64 they execute SSE2; on
any other host they fall back to a scalar path that is bit-identical.

## Where the SIMD lives

The production backing is **C** (the Rust seed is bootstrap-only): native builds
run the C kernels; the interpreter is the seed and uses a thin Rust shim.

- **Production kernels (C, native):**
  `src/runtime/runtime_simd_dispatch.c` — `engine2d_simd_fill_row_u32_api`,
  `engine2d_simd_copy_row_u32_api`, `engine2d_simd_blend_row_u32_api`.
  - fill → NEON `vdupq`/`vst1q` (AVX2 `_mm256_set1_epi64x` on x86); copy →
    `vld1q`/`vst1q`; blend → NEON `mul.4s`/`mla.4s` per-channel multiply-
    accumulate with a **scalar exact `/255` floor** (bit-identical to the Simple
    reference — proven exhaustively over all 16.7M `(sa, s, d)` combinations).
  - Pixels are packed `int64_t` (low 32 = `0xAARRGGBB`); 2 pixels per 128-bit
    NEON vector. Compiled into the core-c runtime archive
    (`pipeline/native_project/tools.rs` runtime input list).
- **Interpreter shim (Rust *seed*):** `compiler/src/interpreter_extern/simd.rs`
  implements the same three `engine2d_simd_*_row_u32_api` facades (fill/copy reuse
  the `engine2d_simd_ops.rs` NEON helpers so the hit counter advances; blend is a
  bit-exact scalar loop), registered in `interpreter_extern/mod.rs` and
  allow-listed in `common/src/runtime_symbols.rs`. The interpreter passes an
  `Arc` clone, so these are **return-style** (a new row is returned and scattered
  back) — the one signature that works in both interpreter and native.
- Simple surface: `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl`
  (`extern fn` declarations + `native_simd_pixel_evidence()`); the other
  `*/gpu/engine2d/simd_kernels.spl` are re-export facades over it.

## Proof it is genuine (not a scalar false-green)

Three independent checks, because this area has a documented history of
scalar-pretending-to-be-NEON false-greens:

1. **Disassembly** — `vdupq_n_u32` lowers to `dup.4s v0, v0[0]` and the kernel
   stores via `str q0` (128-bit NEON register). Real AArch64 NEON, confirmed in
   the built driver.
2. **Bit-identical output** — the native kernel result is compared, byte-for-
   byte, against an independent scalar reference computed in Simple.
3. **Execution counter** — the historical `simd_engine2d_neon_hits()` counter
   now advances for native row chunks on both aarch64 NEON and x86 SSE2. The
   CPU-SIMD evidence gate fails on x86/aarch64 if the counter does not advance
   (`native_simd_executed`), closing the old false-green where the path reported
   a SIMD feature without running vector code.

The gate (`scripts/check/check-cpu-simd-engine2d-evidence.shs`) reports
`native_simd_executed`, `native_simd_bit_exact`, and `native_simd_hits`.
Current Linux x86_64 evidence:
`doc/09_report/cpu_simd_engine2d_evidence_2026-07-08.md` reports
`feature=avx2`, `native_simd_executed=true`, `bit_exact=true`, `hits=2`, and zero mismatch
counts for fill, copy, alpha, scroll, and the 192-pixel diagram. Prior Apple
aarch64 evidence remains in `doc/09_report/cpu_simd_engine2d_evidence_2026-06-09.md`.

## Interpreter vs AOT

The live CPU-SIMD session (`cpu_simd_session.fill_span` → `simd_fill_row`, and
`alpha_blend_span` → `simd_blend_row`) routes solid fills and src-over blends
through native row kernels on x86/aarch64, so the path literally named "CPU SIMD"
genuinely executes vector code (verified: `fill_span` advances the native row
hit counter and stays bit-identical; the blend gate reports
`alpha_mismatch_count=0`). The exact
`/255` floor is reproduced (NEON multiply-accumulate + scalar divide), so the
blend is byte-for-byte identical to the scalar reference — no quality loss.
`blit`/`scroll` stay pure-Simple scalar: they are in-place sub-range copies that
a return-style row kernel can't express without extra marshalling, and they were
never Rust-backed.

Under the tree-walking interpreter a `[u32]` array is a boxed `Vec<Value>`, so
the fill kernel builds a packed native row in the runtime and then copies it into
the framebuffer element-by-element. The vector instructions genuinely execute over
the packed buffer (that is what the disassembly and counter prove); the per-row
copy is an interpreter artifact, not a speedup, and it disappears under AOT
compilation where the framebuffer is already a packed buffer the kernel fills in
place. Note the separate `backend_software` raster loops (used by the non-SIMD
`SoftwareBackend`/`CpuBackend`) keep their own inlined `self.buf[idx] = color`
scalar stores and do **not** call these kernels; routing those through the SIMD
layer is tracked as future work and is gated on the array un-boxing that AOT
provides.

## Verification gates

- `scripts/check/check-engine2d-simd-c-kernels.shs` — compiles the C kernels'
  pure helpers and runs the **exhaustive** bit-exactness test
  (`test/09_baselines/engine2d_simd/engine2d_simd_c_test.c`, all 16.7M
  `(sa,s,d)` blend combos). This is the only gate that exercises the **C** path
  directly; the others run in the interpreter (Rust seed shim).
- `scripts/check/check-cpu-simd-engine2d-evidence.shs` — interpreter evidence
  (x86/NEON executed + bit-exact on capable hosts). Its skip-guard checks the
  `engine2d_simd_fill_row_u32_api` facade so a binary without the new externs
  skips cleanly rather than crashing.
- `scripts/check/check-llvm-simd-row-native-arch.shs` — strict hosted LLVM
  x86_64, AArch64, and RVV binary gate. RVV is an explicit opt-in through
  `SIMPLE_RUNTIME_RISCV64_VECTOR=1` and must run only on an RVV-capable CPU.

## Deployment

Because these are runtime externs, the production `bin/release` binary picks
them up via the standard bootstrap (`scripts/bootstrap/bootstrap-from-scratch.sh
--deploy`). The freshly built driver
(`src/compiler_rust/target/bootstrap/simple`) has them immediately for
verification.

### Open follow-ups

- **Imported array syntax.** Hosted LLVM exact-output probes currently use
  `rt_array_len` / `rt_array_get` because imported `[u32]` `.len()` and indexing
  still lower incorrectly. See
  `doc/08_tracking/bug/llvm_imported_array_len_index_runtime_handle_2026-07-10.md`.
- **Dead legacy handlers.** The old `rt_simd_fill_row_u32` / `rt_simd_copy_row_u32`
  interpreter handlers (engine2d_simd_ops Rust backing) are no longer referenced
  by `.spl`; delete-unused cleanup is deferred to avoid an extra seed rebuild.
- **blit/scroll** remain pure-Simple scalar (never Rust-backed); a genuine SIMD
  win there needs in-place externs, which the interpreter's Arc-clone model can't
  propagate.
