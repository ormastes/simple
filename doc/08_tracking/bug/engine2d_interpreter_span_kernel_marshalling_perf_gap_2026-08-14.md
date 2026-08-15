# engine2d interpreter span kernels 180–300× slower than C due to per-element marshalling

- **Date:** 2026-08-14
- **Status:** OPEN
- **Area:** lib/engine2d + interpreter extern array ABI
- **Severity:** perf (correctness is bit-exact; parity specs green)

## Measurements (same host, x86_64 AVX2, 2026-08-14)

C kernels (`test/09_baselines/engine2d_simd/engine2d_simd_opaque_span_bench.c`,
7680-px spans, p50):

| kernel | C SIMD ns/px | Pure-Simple interp ns/px | gap |
|--------|-------------|--------------------------|-----|
| fill   | 0.17 (1332ns/7680px) | ~31 (8ms / 400×640px)  | ~180× |
| copy   | 0.19 | ~47 (12ms) | ~250× |
| blend  | 0.83 (image span) | ~250 (64ms) | ~300× |

Simple side: `bin/simple run test/perf/graphics_2d/bench_span_kernels.spl`
(`SPAN_BENCH arch=x86_64 native_rows=true`, 400 iters × 640 px).

## Root cause

`src/lib/nogc_sync_mut/gpu/engine2d/simd_kernels.spl` (`simd_fill_row`,
`simd_blend_row`) must gather/scatter the boxed `[u32]` framebuffer
element-by-element around each native row call, because the interpreter
passes an Arc clone so in-place mutation can't propagate (noted in the file's
"Native-SIMD routing gate" comment). The native kernel itself runs real AVX2;
the 180–300× is pure marshalling + interpreted loop overhead.

## Fix direction

Give the interpreter extern ABI a way to pass a `[u32]` buffer by reference
(pinned data pointer) to `rt_engine2d_simd_*_span_u32`, as AOT already does
with packed i64 buffers — then delete the gather/scatter loops. Alternative:
route `fill_span`/`alpha_blend_span` whole-span through the existing
`rt_engine2d_simd_fill_span_u32` in-place ABI in interpreter mode too.

## Attempt 2026-08-15 (reverted — findings recorded, still OPEN)

Tried the "route whole spans through the in-place span ABI" direction and had
to revert. What was learned (all verified empirically on the seed interpreter):

1. **Interpreter `Value::Array` is `Arc<Vec<Value>>`** (compiler/src/value.rs
   :1190); extern handlers receive Arc clones, so a handler can never mutate
   the caller's array (same limitation documented at
   interpreter_extern/simd.rs:247 for rt_aes128_encrypt_block_into).
2. **`mut` array params propagate MUTATION but not REBINDING.** In a callee,
   `b[0] = 9` and `b.push(x)` propagate to the caller's variable; `b = <new
   array>` silently does NOT (and after a rebind, later element writes stop
   propagating too). So `buf = rt_engine2d_simd_fill_span_u32(buf, ...)`
   inside `simd_fill_row` cannot work; write-back requires the per-element
   scatter loop or a bulk mutating channel.
3. **An extern-dispatch write-back interceptor does not work either.** A seed
   patch in `call_extern_function` (interpreter_extern/mod.rs:2769) that
   `env.insert`ed the returned span back onto the dst argument identifier had
   NO effect at any frame depth — the hot extern calls evidently do not
   route through that arg-expression path (or the env store is not the
   channel that relays mutations across frames; `write_back_mutable_arguments`
   in interpreter_call/core/function_exec.rs:1006 looks like it should relay
   whole-value rebinds but observably does not). Result with lib rerouted to
   span kernels + interceptor: fill/blend/blit became NO-OPS in nested frames
   — bench checksum changed 316643543 -> 297684770 (= checksum of the raw
   unblended pattern). Reverted both lib and seed edits; checksum verified
   restored to 316643543.
4. **The parity checksum gate has a pre-existing hole**: the native row blend
   diverges from `_scalar_blend_row` on 350/640 pixels of the bench's varied
   pattern (probe: `engine2d_simd_blend_row_u32` == `rt_engine2d_simd_blend_
   span_u32` != scalar; scalar-mode bench checksum is 948743592 vs native
   316643543), i.e. `SIMPLE_2D_SIMD=off` vs `auto` are NOT byte-identical on
   arbitrary (non-canonical-alpha?) pixel patterns today. Worth its own look.

Next viable directions (not yet done):
- Add a **bulk in-place array primitive** on the interpreter's mutating-method
  channel (interpreter_method/collections.rs + MUTATING_METHODS allow-list in
  interpreter_method/mod.rs:1915), e.g. `arr.write_span(src, dst_off, src_off,
  count)` — that channel is proven to propagate through nested `mut` params
  (`push` does). Needs an AOT/native-codegen counterpart before simd_kernels
  can call it unconditionally.
- Or find/fix why `write_back_mutable_arguments` does not relay rebinds — if
  rebinding a `mut` array param propagated, the return-style span kernels
  could be used directly with zero new surface.

Pending verification commands for whichever fix lands (blocked at revert time
by a repo-wide bootstrap resource lock; a seed rebuild was in flight):
`bin/simple run test/perf/graphics_2d/bench_span_kernels.spl` (checksum must
stay 316643543), `timeout 280 bin/simple test
test/01_unit/lib/gpu/engine2d/simd_kernels_config_matrix_spec.spl` (15/15) and
`.../simd_kernels_spec.spl` (note: one source-shape test there,
"uses the cross-mode return-array span bridge for backend fills", is currently
red from ANOTHER session's uncommitted backend_software.spl edit that removed
the literal `_scalar_fill_row(self.buf, offset as i64, count as i64, color)` —
pre-existing, not part of this bug).

## Non-goals

AOT/native builds are NOT affected (packed framebuffer, kernels run in place).
This is interpreter-lane only.
