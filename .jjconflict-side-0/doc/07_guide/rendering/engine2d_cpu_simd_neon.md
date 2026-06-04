# Engine2D CPU SIMD — genuine NEON on aarch64

The CPU ("software") engine2d backend's hot pixel-row kernels are backed by
real SIMD instructions, not scalar loops that merely *report* `has_neon`. On
aarch64 the fill and copy spans execute NEON; on x86_64 they execute SSE2; on
any other host they fall back to a scalar path that is bit-identical.

## Where the SIMD lives

- Kernels: `src/compiler_rust/runtime/src/value/engine2d_simd_ops.rs`
  - `fill_row_u32` → NEON `vdupq_n_u32` + `vst1q_u32` (SSE2 `_mm_set1_epi32` +
    `_mm_storeu_si128`).
  - `copy_row_u32` → NEON `vld1q_u32` + `vst1q_u32` (SSE2 load/store).
  - A `SIMD_ROW_HITS` counter increments only when a real SIMD chunk runs, so
    evidence can prove NEON executed instead of the scalar fallback.
- Interpreter dispatch: `compiler/src/interpreter_extern/simd.rs`
  (`rt_simd_fill_row_u32`, `rt_simd_copy_row_u32`,
  `rt_simd_engine2d_neon_hits`, `rt_simd_engine2d_neon_reset`), registered in
  `interpreter_extern/mod.rs` and allow-listed in
  `common/src/runtime_symbols.rs` (`RUNTIME_SYMBOL_NAMES`).
- Simple surface: `src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl`
  (`extern fn` declarations + `native_simd_pixel_evidence()`).

## Proof it is genuine (not a scalar false-green)

Three independent checks, because this area has a documented history of
scalar-pretending-to-be-NEON false-greens:

1. **Disassembly** — `vdupq_n_u32` lowers to `dup.4s v0, v0[0]` and the kernel
   stores via `str q0` (128-bit NEON register). Real AArch64 NEON, confirmed in
   the built driver.
2. **Bit-identical output** — the native kernel result is compared, byte-for-
   byte, against an independent scalar reference computed in Simple.
3. **Execution counter** — `rt_simd_engine2d_neon_hits()` only advances on the
   NEON chunk path. The CPU-SIMD evidence gate now *fails* on aarch64 if the
   counter did not advance (`native_simd_executed`), closing the old false-green
   where the path reported `has_neon` without running NEON.

The gate (`scripts/check/check-cpu-simd-engine2d-evidence.shs`) reports
`native_simd_executed`, `native_simd_bit_exact`, and `native_simd_hits`.
Verified result on Apple aarch64: `executed=true bit_exact=true hits=2`.

## Interpreter vs AOT

The live CPU-SIMD session (`cpu_simd_session.fill_span` → `simd_fill_row`)
routes solid fills through the NEON kernel on aarch64, so the path literally
named "CPU SIMD" genuinely executes NEON (verified: `fill_span` advances the
NEON hit counter and stays bit-identical). Blend and blit stay scalar: an exact
NEON divide-by-255 differs from the scalar floor (and Metal has no blend
kernel), and a boxed-array copy is already memcpy-equivalent.

Under the tree-walking interpreter a `[u32]` array is a boxed `Vec<Value>`, so
the fill kernel builds a packed NEON row in the runtime and then copies it into
the framebuffer element-by-element. The NEON instructions genuinely execute over
the packed buffer (that is what the disassembly and counter prove); the per-row
copy is an interpreter artifact, not a speedup, and it disappears under AOT
compilation where the framebuffer is already a packed buffer the kernel fills in
place. Note the separate `backend_software` raster loops (used by the non-SIMD
`SoftwareBackend`/`CpuBackend`) keep their own inlined `self.buf[idx] = color`
scalar stores and do **not** call these kernels; routing those through the SIMD
layer is tracked as future work and is gated on the array un-boxing that AOT
provides.

## Deployment

Because these are runtime externs, the production `bin/release` binary picks
them up via the standard bootstrap (`scripts/bootstrap/bootstrap-from-scratch.sh
--deploy`). The freshly built driver
(`src/compiler_rust/target/gui/debug/simple`) has them immediately for
verification.
