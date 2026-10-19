# Seed JIT: defensive array copies are never freed (quadratic leak)

- **Date:** 2026-10-19
- **Lane:** Rust seed, `SIMPLE_EXECUTION_MODE=jit` (Cranelift)
- **Status:** mitigated (the `Let` place copy now moves when its source is provably dead and unique, plus a zstd hot-loop rewrite). The general problem and the pre-existing struct-literal aliasing are DEFERRED.

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
2. *(Superseded; see "Review follow-up" below.)* Struct literals briefly copied
   `var` array arguments. That was reverted because the copy is never freed: it
   leaked through projections (128 KiB zstd decode 280 MB → 2.0 GB) and through live
   `var`s reused in loops (39 MB → 2.46 GB).
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

## Review follow-up: struct literals never copy (option A, 2026-10-19)

The struct-literal copy of a `var` array (item 2 under "What changed") was removed
again. A `var` that is still LIVE after the literal got a copy that is never freed,
so a buffer reused in a loop (`b.push(x); st = S(buf: b, n: i)`) leaked one growing
copy per iteration.

| n=65536 loop | base JIT | with copy (`2731e01c…`) | final (`ce2a6a11…`) |
|---|---|---|---|
| RSS | 37 MB | **2.46 GB** | 39 MB |

- Struct literals now lower exactly as base.
- A `var` whose every struct-literal use is proven dead is "handed over" and keeps the
  struct uniquely owned.
- Any other array argument shares its buffer, so the struct is not unique. This is a
  fixpoint over the hand-over set.
- `@inject`-constructor types are never unique (the literal lowers to a call).
- Every non-primitive slot (`Any`, generic, nested aggregate) needs a private buffer.
- MIR `rt_array_copy` counts on all fixtures now equal base; the repro drops by 1.
- Final binary `ce2a6a11…fefad041a`. All 30 fixtures × 2 engines plus the alias probe
  match base output.

## DEFERRED

- **Refcount or ownership reclamation on the JIT lane.** `out = f(out)` across a call is
  still one leaked copy per call (callee-side `var out = buf`). The same pattern remains
  in `lz4.spl` (`_lz4_append_bytes`, lines 191-233 and 375), `snappy.spl`,
  `lzma2_xz_format.spl`, `lzma2_chunk_decoder.spl`, `gzip.spl`, and `zstd_dict.spl`
  (`append_bytes` per block).
- **Pre-existing JIT aliasing bug (kept as base):** a struct literal stores its array
  argument's handle. After `st = St(output: o); o.push(4)` the JIT reports
  `st.output.len() == 4`; the interpreter reports 3. The same holds for projections,
  params and `val`s.
  - Pinned by `alias_probe_pins_base_aliasing`
    (`compiler/tests/jit_struct_array_field_leak.rs`).
  - Fixing it needs reclamation or refcount: a copy at the literal is never freed and
    leaks (39 MB → 2.46 GB on the loop above; 280 MB → 2.0 GB on a 128 KiB zstd
    decode).
- **Port to the self-hosted lane:**
  - Port the move analysis into `src/compiler/50.mir/mir_lowering_stmts.spl`
    (`maybe_copy_array_value`).
  - `Drop` is a no-op there too (`70.backend/backend/_MirToLlvm/core_codegen.spl`).
  - Struct literals do not copy `var` arrays there either.
