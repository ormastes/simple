# Seed JIT: defensive array copies are never freed (quadratic leak)

- **Date:** 2026-10-19
- **Lane:** Rust seed, `SIMPLE_EXECUTION_MODE=jit` (Cranelift)
- **Status:** mitigated (two copy sites now move instead of copying, plus a zstd hot-loop rewrite); the general problem is DEFERRED

## Root cause

- `compiler/src/mir/lower/lowering_stmt.rs` (`is_array_place_alias`): a `Let` of array type
  whose initializer is a place (`var o = st.output`, `var out = buf`) always emits
  `rt_array_copy`, a full O(len) copy that keeps arrays value types.
- Nothing on the JIT lane ever frees an array. `MirInst::Drop` is a no-op
  (`compiler/src/codegen/instr/mod.rs`, the `MirInst::Drop` arm), no lowering emits
  `rt_array_free`, and runtime arrays have no refcount.
- So `var o = st.output; o.push(x); st = St(output: o)` keeps one full stale copy per
  round-trip: memory and time both grow quadratically. The interpreter is linear
  because it uses Arc clones and copies only on mutation (`Arc::make_mut`).
- zstd hits the same leak through a call: `out = append_bytes(out, ...)` once per
  sequence (`src/lib/common/compress/zstd_seq.spl`). The callee re-binds its parameter
  (`var out = buf`), which copies the whole output on every call.
- Related existing bug: a struct literal built from a `var` array stored the handle
  without copying. After `st = St(output: o); o.push(4)`, the JIT gave `st.output.len() == 4`;
  the interpreter gives 3.

## What changed

1. `compiler/src/mir/lower/array_move.rs` (new) works out, per function, which copies
   can move the buffer instead. It is conservative: if it cannot prove the source is
   uniquely owned and dead, the copy stays.
   - **Site A:** a `Let` of an array from `Local(s)` or `s.f`. The source `s` must be a
     non-parameter local, uniquely owned, and dead afterwards (provable by a forward scan
     of the same statement list).
   - **Site B:** a `var` array local passed as a struct-literal field, when every such
     use of it is dead afterwards (the next point is overwrite or end of scope, or it
     sits inside a `return`).
   - **Disqualifiers:** parameters, call-built sources, `val saved = st`, lambda
     captures, `defer`, generators/async, field stores of arrays, `break`/`continue`
     between the copy and the overwrite, any later mention (including in nested
     blocks), and an overwrite whose right-hand side reads the source.
2. `lowering_expr_struct.rs` now copies a `var` array local that is passed as a
   struct-literal field, unless step 1 proved it dead. This fixes the aliasing bug
   above.
   - **Scope narrowed on evidence.** Copying every array place there (projections,
     params, `val`s) re-created the leak through the functional-update idiom
     `S(data: st.data, ...)`, which `zstd_bits.spl` runs once per bit read. Measured on
     a 128 KiB zstd decode under JIT: 280 MB became 2.0 GB.
   - Those arguments therefore keep the base aliasing, and a struct built from one is
     treated as not uniquely owned.
3. `src/lib/common/compress/zstd_seq.spl` `_zstd_execute_sequences` now appends
   literals and match copies in place, with the same checks and error messages as
   before.

## Measurements

Binaries: base `8dd88736…f2960cd3`, fix `2731e01c…fde3263d` (the final committed tree, after a rustfmt/comment-only pass, builds `2a5796fd…c658a033`; spot-checked on repro n=65536, the 128 KiB zstd decode and the alias probe on both engines, with the same results).

Method: 5 runs per cell, median shown. Each run was capped at `MemoryMax=6G`, with the
host shared.

| case | base JIT | fix JIT | base interp | fix interp |
|---|---|---|---|---|
| repro n=16384 | 73 MB, 0.06 s | 39 MB, 0.06 s | 40 MB, 0.15 s | 41 MB, 0.15 s |
| repro n=65536 | 697 MB, 0.09 s | 40 MB, 0.06 s | 56 MB, 2.0 s | 57 MB, 1.98 s |
| zstd 16 KiB (old lib → new lib) | 726 MB → 236 MB | 728 MB → 242 MB | 107 → 105 MB, 0.94 → 0.80 s | 108 → 106 MB |
| zstd 32 KiB | 1.93 GB → 243 MB | 1.93 GB → 245 MB | 1.76 → 1.31 s | 1.77 → 1.31 s |
| zstd 64 KiB | OOM at 6 GB → 253 MB | OOM → 251 MB | 4.40 → 2.37 s | 4.36 → 2.39 s |
| zstd 128 KiB | OOM at 6 GB → 261 MB, 0.74 s | OOM → 257 MB, 0.75 s | 13.7 → 4.53 s | 13.4 → 4.51 s |

- **Output checks:** every decode matches `zstd -dc` byte for byte. The Simple
  compress → decompress round-trip is identical on all four sizes, on both engines and
  both binaries, and `zstd -dc` accepts every Simple-compressed frame.
- **Fixtures:** all 41 files in `test/fixtures/engine_differential` give identical stdout
  on base and fix, including `packed_array_value_semantics`. Total wall time is within
  noise (JIT 3.04–3.19 s vs 3.09–3.21 s).
- **MIR `rt_array_copy` count:**
  - Repro: 1 → 0.
  - Alias probe: 1 → 2. The new copy is the aliasing fix.
  - `DataFrame.from_columns`, `concat_cols`, `merge_by_pairs`, `check_package_pins` and
    `process_inspection_owner_start_pinned_v1`: +1 to +3 each. These are one-shot
    construction copies of `var` arrays that are read (passed to a call, compared) after
    the struct literal.
  - Nothing else changed.

## BLOCKER: new leak shape from the struct-literal copy (found in review, 2026-10-19)

A `var` array that is still LIVE after a struct literal is now copied, and the JIT
never frees that copy. Base aliased it instead (no copy, wrong value semantics). Reusing
the buffer in a loop therefore keeps one growing copy per iteration:

```
var b: [u8] = []
while i < n:
    b.push(x)
    st = S(buf: b, n: i)
```

| n | base JIT | fix JIT (`2731e01c…`) | base interp | fix interp |
|---|---|---|---|---|
| 16384 | 38 MB, 0.07 s | 185 MB, 0.06 s | 39 MB, 0.78 s | 40 MB, 0.77 s |
| 65536 | 39 MB, 0.05 s | **2.46 GB**, 0.17 s | 57 MB, 15.5 s | 58 MB, 17.3 s |

- Value semantics make this pattern O(n²) copies on every engine: the interpreter takes
  15 s and survives only because it frees.
- So the copy is semantically right but cannot ship on a lane with no reclamation.
- Option A: never copy at struct literals. A proven-dead `var` still moves; a live one
  aliases exactly as base and makes the receiving struct non-unique.
- Option B: keep the copy and accept this shape until reclamation lands.
- Decision pending.

Review hardening, also in this lane:

- A type with an `@inject` `new` lowers its literal to a constructor call, which skips
  the copy. Its literals are now never uniquely owned, and their arguments count as
  escaping (same behaviour as base).
- Every non-primitive struct slot must get a private buffer, so an `Any` or generic slot
  holding an array, or a nested aggregate argument, makes the struct non-unique.

## DEFERRED

- **Refcount or ownership reclamation on the JIT lane.** `out = f(out)` across a call is
  still one leaked copy per call (callee-side `var out = buf`). The same pattern remains
  in `lz4.spl` (`_lz4_append_bytes`, lines 191-233 and 375), `snappy.spl`,
  `lzma2_xz_format.spl`, `lzma2_chunk_decoder.spl`, `gzip.spl`, and `zstd_dict.spl`
  (`append_bytes` per block).
- **Struct literals from projections, params and `val`s still share the buffer** (base
  behaviour). The right fix needs reclamation, not more copies.
- **Port to the self-hosted lane:**
  - Port the move analysis into `src/compiler/50.mir/mir_lowering_stmts.spl`
    (`maybe_copy_array_value`).
  - `Drop` is a no-op there too (`70.backend/backend/_MirToLlvm/core_codegen.spl`).
  - Struct literals do not copy `var` arrays there either.
