# engine2d interpreter span kernels 180–300× slower than C due to per-element marshalling

- **Date:** 2026-08-14
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
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

## Resolution 2026-08-15 — bulk in-place `arr.write_span` primitive

Implemented the doc's first "next viable direction": a bulk mutating array
method `arr.write_span(src, dst_off, src_off, count)` (copies
`src[src_off..+count]` into `self[dst_off..+count]`, bounds-checked with no
silent growth, `count<=0` no-op returning 0, returns count written,
memmove-style overlap semantics — src is snapshotted at argument evaluation).

Surfaces:
- **Interpreter (seed):** shared kernel `array_write_span` in
  `compiler/src/interpreter_method/collections.rs`; identifier fast path in
  `interpreter_helpers/patterns.rs` (ownership-gated `Arc::make_mut`, added to
  `ARRAY_MUTATING_METHODS`); place write-back special case (like `pop`) in
  `interpreter_method/mod.rs` + `MUTATING_METHODS`. Proven to propagate
  through nested `mut` params exactly like `push`.
- **Seed JIT:** `rt_array_write_span` (runtime/src/value/collections.rs,
  in-place on the heap array, `copy_within` for same-array overlap, returns a
  tagged int), dispatch arms in `codegen/instr/calls.rs` and
  `codegen/instr/closures_structs.rs`, registered in `runtime_sffi.rs` +
  `common/src/runtime_symbols.rs`.
- **Lane gate:** new `rt_is_jit_runtime()` (Rust runtime flag set by the
  driver around `run_file_jit` main execution; `false` stub in the C runtime
  `src/runtime/runtime.c`). `simd_kernels.spl` routes its fill/blend/blit
  scatter/gather loops through `_write_span_bulk` only when
  `rt_is_interpreter_runtime() or rt_is_jit_runtime()` — self-hosted AOT
  lowering has no write_span counterpart yet, so AOT keeps the element loops
  (and AOT never needed the bridge: packed buffers run kernels in place).

Measured (same host/bench, `bin/simple run test/perf/graphics_2d/bench_span_kernels.spl`):

| kernel | before ms | after ms |
|--------|-----------|----------|
| fill   | 8         | 7 (dominated by the extern row build, no longer the scatter) |
| copy   | 12–17     | **0** |
| blend  | 63–71     | **26** |
| blit   | 12–21     | **0** |

Checksum stayed **316643543**. `SIMPLE_2D_SIMD=off` now also yields 316643543
(the scalar/native blend divergence flagged in finding 4 was fixed separately
by the blend-formula lane; off and auto agree with each other). Pure
interpreter micro-bench of the scatter itself: 400×640 px, per-element loop
650.7ms vs `write_span` 6.8ms (**~96×**).

Important lane discovery recorded for future readers: the bench file JITs
(its `println` even proves it — the interpreter rejects `println`), so the
numbers in the table above are the seed-JIT lane; the pure-interpreter lane
improvement is the 96× micro-bench. Both lanes are covered by the gate.

Specs: new `test/01_unit/lib/gpu/engine2d/array_write_span_spec.spl` (6/6:
bounds/no-growth, zero-count, overlap fwd+back memmove semantics, nested-mut
propagation); `simd_kernels_config_matrix_spec.spl` 18/18;
`simd_kernels_branch_coverage_spec.spl` 26/26; `simd_kernels_spec.spl` 50/51
(the 1 red is the pre-existing "cross-mode return-array span bridge"
source-shape test from another session's uncommitted backend_software.spl
edit, noted above).

Follow-up (small, not blocking): give the self-hosted AOT lowering
(`src/compiler/50.mir`) a `write_span -> rt_array_write_span` arm and then
widen `_bulk_span_ready()`; consider building the fill row without the extern
return-array round trip to shave the remaining fill ms.

### Follow-up DONE 2026-08-15 — AOT lowering landed, gate removed

- MIR: `lower_unresolved_array_write_span` in
  `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`, hooked at
  both unresolved-builtin-method sites next to `push` (args.len()==4), plus
  `write_span` added to `is_mutating_method` (switch_operators_calls.spl) so
  Index/Field receivers get the same write-back as `push`.
- Backend decls: `declare i64 @rt_array_write_span(ptr, ptr, i64, i64, i64)`
  registered in `_MirToLlvm/asm_constraints_helpers.spl` (declare +
  defined_func_names + param/return types), `llvm_lib_translate.spl`,
  `llvm_backend.spl`, `llvm_backend_tools.spl`.
- C runtime: `rt_array_write_span` added to `src/runtime/runtime_native.c`
  (+ decl in `runtime.h`) — same contract as the seed runtime's
  (count copied / -1 OOB / 0 for count<=0), memmove for same-storage
  (overlap-safe), per-element get/set for mixed bytes-vs-i64 storage.
  `clang -fsyntax-only` clean.
- `_bulk_span_ready()` + `rt_is_interpreter_runtime`/`rt_is_jit_runtime`
  externs removed from `simd_kernels.spl`; all lanes now use `write_span`
  (element-loop fallbacks deleted).
- Verified: `array_write_span_spec.spl` 6/6, `simd_kernels_config_matrix_spec`
  18/18, `simd_kernels_spec` 51/51 (interpreter lane, 2026-08-15).
- Review fixes (Opus, 2026-08-15): (a) the C memmove fast path now requires
  BOTH the BYTES and U64_PACKED flags to match (packed slots hold raw u64,
  unpacked non-bytes slots hold TAGGED values — a bit copy across that
  boundary corrupts, e.g. engine2d's `[u32]` shapes); the cross-layout
  fallback normalizes each element to a raw u64 and re-encodes for the
  destination (rt_value_as_u64 / rt_core_value_u64_compact, same pattern as
  the rt_typed_words_* accessors — the plain rt_array_get/set pair is
  packed-blind and was NOT reused). (b) The RuntimeValue-ABI declare lanes
  (`llvm_backend.spl`, `llvm_backend_tools.spl`, `llvm_lib_translate.spl`)
  return `ptr` (tagged RuntimeValue, sibling-consistent with their
  `ptr @rt_array_push(ptr, ptr)`); the C-ABI lane
  (`asm_constraints_helpers.spl`) stays raw `i64`. (c) Bounds check adds
  explicit `count > len` guards ahead of `off > len - count` so the
  subtraction can never underflow (the Rust impl's `dst_off + count >
  dst_len` form has the analogous i64-overflow edge for pathological counts
  — noted, not changed here).
- Packed-vs-boxed regression test: NOT expressible as an interpreter spec —
  `bin/simple test` runs on the Rust seed runtime, which never calls the C
  `rt_array_write_span`, and the C U64_PACKED layout (rt_array_new_u64 /
  rt_typed_words_*) has no pure-Simple constructor on that lane. The
  cross-layout branch is therefore covered by the pending AOT probe below,
  not by a faked spec.
- **PENDING AOT verification** (bootstrap was running; no admitted stage
  binary to compile with at the time): after the next bootstrap deploys a
  self-hosted `bin/release/<triple>/simple`, compile+run a probe that does
  `var d=[0,0,0,0]; var s=[1,2,3,4]; d.write_span(s,1,0,2); print(d[1]); print(d[2])`
  under the pure-Simple AOT backend and expect `1`/`2`; also re-run
  `sh scripts/check/check-simpleos-qemu-engine2d-simd-kernels.shs` for the
  end-to-end lane. Until that runs, the AOT arm is code-reviewed +
  interpreter-spec-verified only.

## Non-goals

AOT/native builds are NOT affected (packed framebuffer, kernels run in place).
This is interpreter-lane only.
