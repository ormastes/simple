# Native pure-Simple XXH3 is ~35-40x slower than the runtime: every 8-byte load is a locked registry lookup + 8-slot gather (2026-10-27)

**Status:** OPEN (perf; compiler/runtime, not fixed here)
**Severity:** P2. Correct output, but the pure-Simple fallback hashes at ~200 MB/s vs ~7000 MB/s for `rt_xxh3_128_text`.
**Found by:** XXH3 lane native benchmark, stage2 `C:/dev/p3new/stage2.exe` `native-build`, Windows x64, clang64 + MSVC link.

## Numbers (one native exe, `rt_time_now_unix_micros`, 64 KB `[u8]`)
| bench | work | time | ns/op |
|---|---|---|---|
| a | 1e8 x (u64 mul+add, shr+xor) in locals | 336 ms | 3.4 per iter (~0.85 per op) |
| b | 1e7 x `_xxh64_load_u64_le(buf, off)` | 180 ms | 18.0 (14.2 net of 3.8 loop) |
| c | 1e7 x `buf[i].to_u64()` | 135 ms | 13.5 (9.7 net) |
| c2 | loop + `%` only | 38 ms | 3.8 |
| d | 1e7 x empty `fn(a: [u8], o: i64) -> u64` | 21 ms | 2.1 |
| e | full `xxh3_64` over 64 KB (avg of 5) | 332 us | ~198 MB/s |

Model: 1024 stripes x 16 loads x 18 ns = 295 us = **~89 %** of (e). Arithmetic
(~64 ops x 0.85 ns x 1024 = 56 us worst case, less in practice) and the empty
call/array-arg overhead (d: 2 ns, so no refcount/copy on array args) are minor.
Loads are the gap; arithmetic and calls are not.

## Top cause: `rt_typed_bytes_u64_le_at` is an opaque call that validates the array through a locked global registry
Disassembly of the native exe (`llvm-objdump -d`; binary is stripped, found by the
`_hash_long_acc` shape):
- `_hash_long_acc` stripe body is already clean: u64 locals live in raw registers/stack,
  `and/shr/imul/add` inline, **no boxing, no `rt_value_*` calls, no array copies, no refcount
  traffic**. It contains exactly 24 calls to the tiny wrapper `_xxh64_load_u64_le`
  (`sub rsp; call; ret`, never inlined) -> `jmp rt_typed_bytes_u64_le_at`.
- Each `rt_typed_bytes_u64_le_at` call does: (1) a spin lock (`xchg byte ptr [..], al` loop)
  and an open-addressed hash probe (`shr 0x21 / imul / xor / and`) in `0x14000b600`
  to prove the pointer is a live heap object, then (2) tag/len/cap checks, (3) a
  gather of **8 separate 8-byte slots** (`mov edx,[rcx+8*rax]; shr 3; ... shl 0x1d; or ...`).
  That is ~100 instructions + a locked RMW per 8 bytes, vs one `mov rax,[p+off]`.
- Why the gather: `var buf: [u8] = []` + `push` yields the generic slot array
  (`flags & RT_CORE_ARRAY_FLAG_BYTES == 0`, see the `test dl, 8` branch), not a packed
  byte array. The C source of the same function is `src/runtime/runtime_native.c:10994`
  (`rt_bytes_u64_le_at`: per-byte loop with a flag test per byte) and `:11049`.
  Even the `_unchecked` variant (`:11053`) still loops 8 times.
- The Rust seed has an inline lowering for exactly this call
  (`src/compiler_rust/compiler/src/codegen/instr/calls.rs:3889`
  `compile_inline_typed_bytes_le_unchecked`; `codegen/llvm/functions/calls.rs:2058`).
  The pure-Simple compiler has no equivalent: grepping `src/compiler` for
  `rt_typed_bytes_u64_le_at` finds only a purity classification
  (`src/compiler/60.mir_opt/mir_opt/collection_opt_core.spl:720`,
  `is_collection_runtime_read`) and no expansion, so stage2 emits a plain external call.

## Secondary causes
1. Plain `buf[i].to_u64()` costs ~9.7 ns net (c): same registry-validated runtime read path, not an inline load.
2. `_xxh64_load_u64_le` is a non-inlined wrapper (extra call+ret per load, 3 per 2 loads of dispatch); `_hash_long_acc` spills all 8 accumulators and 16 loaded values to the stack (rsp-relative moves), ~0.1 ns each, minor.
3. Half of the per-stripe loads (8 of 16) read the secret. They are NOT loop-invariant: the secret offset is `k = s*8` and advances every stripe (`src/lib/common/crypto/xxh3.spl` `_hash_long_acc`). Only the 8 scramble-key loads at `last_k` (once per block) are invariant. Because the per-stripe secret pattern repeats every block, it could instead be precomputed once into a `per_block*8`-entry u64 table, removing those 8 loads per stripe.

## `[u8]` memory
16,777,216 pushed bytes: native exe peak working set 135.4 MB vs 6.2 MB for an empty exe
-> 129.2 MB / 16.78 M = **~7.7 B/element (8 B tagged slot per byte, ~8x)**. The earlier ~1.1 GB
peak for a 16 MB hash input is therefore ~8 copies of that (input + intermediates held by
the caller), not one oversize array. A packed byte array (`rt_byte_array_new`,
`runtime_native.c:9666`, 1 B/elem) exists but `[u8]` literals/`push` do not select it.

## Proposed fix (expected gain)
1. Pure-Simple compiler: lower `rt_typed_bytes_u64_le_at` / `u32_le_at` (and `u8` index reads) to an
   inline bounds check + single unaligned load when the array is `FLAG_BYTES`, mirroring the seed's
   `compile_inline_typed_bytes_le_unchecked`; hoist the registry validation out of loops
   (once per array per function). Expected: 18 ns -> ~1-2 ns per load, i.e. 295 us -> ~25 us per
   64 KB, **~10x on xxh3_64 (200 -> ~2000+ MB/s)**.
2. Make `[u8]` (literal, `push`, `with_capacity`) allocate `FLAG_BYTES` arrays: 8x less memory and
   makes (1) a plain `mov`. Gets within ~2-3x of the runtime.
3. Cheap runtime-only stopgap: in `rt_bytes_u64_le_at` use `memcpy` for the BYTES case and drop the
   per-byte flag test; replace the spin-locked registry probe by a per-thread last-validated-pointer cache. Expected ~2-3x.
Repro: `.prof/mb.spl` shape above (bench sources are not committed); build with
`stage2.exe native-build mb.spl -o mb.exe`.

## Fix (pending native proof)

`rt_typed_bytes_u64_le_at` / `rt_typed_bytes_u32_le_at` (and the `rt_bytes_*`
spellings) are now lowered inline by the self-hosted LLVM backend
(`_MirToLlvm/core_codegen.spl` `translate_call_at` ->
`asm_constraints_helpers.spl` `emit_inline_typed_bytes_le`), mirroring the Rust
seed's `compile_inline_typed_bytes_le_unchecked`. Hosted x86_64/aarch64
(linux/windows/macos/freebsd) only; freestanding targets keep the call.

Kept per call (cheap, no memory-order cost): heap tag == 1, raw >= 4096, header
kind == array, negative-index wrap, and `0 <= idx <= len - width` (OOB and
non-array still return 0). Dropped: the spin lock + global probe in
`rt_core_is_registered_immortal_ptr` and the `len <= cap` / capacity
re-validation (same trust as the seed's inline path). The lowering is
branch-free (selects against a shared zero global) because the LLVM emitter's
successor phis name `%bbN`, so a call site must not open a new block. Per-loop
hoisting of the validation is NOT done: the MIR optimiser has no loop-invariant
array-validation fact (`typed_byte_canon` is a skeleton), so validation stays
per call, minus the lock.

Expected gain: the ~89% of XXH3 time spent in the registry lock + probe
(plus call overhead) is replaced by ~35 register ops and 2-3 loads per 8 bytes,
i.e. the record's estimate of 18 ns -> a few ns per load (roughly 5-10x on xxh3_64,
200 -> 1000-2000 MB/s; slot-layout arrays decode 8 slots so stay below the
packed-byte ideal), to be measured. Native proof comes
with the next stage2/stage3 rebuild (no compiler was rebuilt for this change);
spec: `test/01_unit/compiler/50.mir/inline_typed_bytes_load_spec.spl`
(IR-level). The Cranelift adapter path is not changed.
