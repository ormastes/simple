# U64 Range For-Loop Checksum Mismatch - 2026-05-14

## Status

**Status: RESOLVED** (checksum correctness). Performance parity remains open.

Rust seed: verified end-to-end (unit test + benchmark parity).
Self-hosted SPL compiler: source-verified by code inspection; end-to-end run
pending a full bootstrap rebuild.

**Re-verified 2026-05-29:** Rust seed fix confirmed passing at HEAD. Test is
at `src/compiler_rust/compiler/src/mir/lower/tests/branch_coverage/control.rs`
(full path: `mir::lower::tests::branch_coverage::control::for_range_preserves_u64_counter_type`).
The earlier doc said "not found in `src/compiler_rust/src/`" — that path was
stale; the correct path is under `src/compiler_rust/compiler/src/`.

**Self-hosted SPL compiler fix (2026-05-29):** The same bug was present in
`src/compiler/50.mir/mir_lowering_stmts.spl` — `lower_for_range` hardcoded
`MirType.i64()` for the counter local and the Add result type, ignoring the
bound expression's actual type. Fixed by:
- Deriving `loop_ty` from the end/start `HirExpr.type_` field (via
  `self.lower_type`) before emitting any code
- Using `loop_ty` for the counter local, the increment BinOp result
- Emitting typed integer constants (`MirConstValue.Int` + `loop_ty`) for
  nil start/step defaults instead of the old i64-typed `emit_const_int`

This ensures all loop temporaries are type-consistent (no i64/u64 width
mismatch), matching the Rust seed's `range_counter_type` logic.

**Code-inspection verified 2026-05-29:** `lower_for_range` in
`src/compiler/50.mir/mir_lowering_stmts.spl` (lines 411–540) was read and
confirmed to match the fix description exactly:
- `loop_ty` derived from `end.unwrap().type_` (falling back to `start`'s type,
  then `MirType.i64()`) via `self.lower_type` — lines 433–438
- `b_init.new_local(nil, loop_ty, LocalKind.Var)` for the counter — line 472
- `MirConstValue.Int(0/1)` with `loop_ty` for nil start/step defaults — lines
  445–466
- `b_inc.emit_binop(MirBinOp.Add, ..., loop_ty)` for the increment — line 516
No hardcoded `MirType.i64()` remains in the range-counter path.

**Note:** A full bootstrap rebuild is needed to verify the SPL fix end-to-end.

## Context

While investigating pure Simple collection parity, converting the verified
`while` loops in `test/perf/collections/collection_simple.spl` to canonical
range `for` loops changed benchmark results instead of preserving behavior.

Probe shape:

```spl
for i in 0..length:
    checksum = checksum + (data[i] ^ iter)
```

where `length` is a cached `u64` from `data.len().to_u64()`.

## Evidence

Command:

```bash
timeout 150s env SIMPLE_COLLECTION_BENCH_SOURCE_CLOSURE=1 SIMPLE_COLLECTION_BENCH_CLEAN=1 SIMPLE_COLLECTION_BENCH_CPU=native test/perf/collections/run_collection_benchmarks.shs
```

Original observed checksum mismatch before the compiler fix:

- C/Rust `list_traverse`: `3865411584000`
- Simple `list_traverse` after the `for 0..length` rewrite: `483124838400`
- Simple `set_contains` after the analogous range rewrite: `0`

The compiler now preserves unsigned counter typing for `for 0..u64_bound`
lowering, and the same benchmark probe preserves checksum parity after
rebuilding `src/compiler_rust/target/debug/simple`.

Resolved evidence:

- `cargo test --manifest-path src/compiler_rust/Cargo.toml -p simple-compiler for_range_preserves_u64_counter_type -- --nocapture`
- rebuilt driver with `cargo build --manifest-path src/compiler_rust/Cargo.toml -p simple-driver --bin simple`
- reran the collection benchmark probe with `for 0..length`; all four
  benchmark checksums matched C/Rust

The probe was still reverted. Keep the collection benchmark on the faster
verified `while` form until range-for optimization performance catches up.

## Impact

The existing SIMD/reduction optimizer only analyzes canonical range `for`
loops, but the current collection benchmark still should not be converted to
that shape because it regressed speed sharply even after checksum correctness
was fixed. Closing the list traversal and scalar membership gaps should either:

- speed up unsigned range-loop lowering/codegen first, or
- add equivalent optimizer support for the existing `while unsigned_index <
  cached_len` shape.
