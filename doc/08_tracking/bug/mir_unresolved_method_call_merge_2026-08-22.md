# MIR lowering has no `merge` arm, but the desugar generates `.merge()` (2026-08-22)

Filed: 2026-08-22
Status: RESOLVED 2026-08-22
Severity: blocker — currently the last wall for MCP/LSP-MCP `--entry-closure` native-builds

## Symptom

```
[mir-lower] WARNING: unresolved method call 'merge' lowered to const-0 placeholder (silent-null risk, Task #145)
error: MIR lowering error: unresolved method call: merge
```

repeated ~20x, aborting the build. Sibling unresolved calls seen in the same run:
`partition`, `new`, `upper`. All of them take the same branch
(`50.mir/_MirLoweringExpr/method_calls_literals.spl:3254-3263`) which BOTH calls
`self.error(...)` and prints the warning, so they are all errors; `merge` merely
dominates by call-site count.

## Why this one is structural rather than an ordinary missing builtin

`.merge()` is **compiler-generated**. `10.frontend/desugar/collection_desugar.spl`
rewrites, at AST level and for every backend:

```
Pattern B:  x = x + other_arr   ->   x.merge(other_arr)
```

with the documented contract "`.merge(arr)` extends the array in-place (O(m))".
So the frontend emits a method the MIR lane cannot lower, for source that never
mentions `merge`. `/usr/bin/grep -n '"merge"' src/compiler/50.mir/**` returns
only an unrelated basic-block label — there is **no** `merge` arm anywhere in MIR
lowering.

## Why it is not a one-line fix

The runtime has no in-place extend. The only related export is

```
SplArray* rt_array_concat(SplArray* a, SplArray* b);   # src/runtime/runtime.h:461
```

which **allocates a new array**. Lowering `.merge` to `rt_array_concat` would
satisfy the type checker while silently breaking the desugar's O(m) in-place
contract — reintroducing exactly the O(n^2) behaviour the desugar exists to
remove, and losing the aliasing semantics of an in-place extend.

A correct fix needs, in order:

1. a new `rt_array_extend(SplArray* dst, SplArray* src)` (in-place, amortized
   O(m)) in the C runtime — note this crosses
   `scripts/check/check-runtime-api-regression-push.shs` and
   `check-c-runtime-compiles-push.shs`;
2. a `merge` arm in `50.mir/_MirLoweringExpr/method_calls_literals.spl` emitting
   it, with the receiver treated as mutated in place;
3. a decision for non-array receivers that legitimately define `merge`
   (`Map.merge`, `PersistentMap.merge`, `SdnSpan.merge`) so the arm does not
   capture them.

## Adjacent smells worth checking first

- `src/lib/common/sdn/value.spl:18` declares `fn merge(self, other: SdnSpan)` —
  the `fn ... (self, ...)` form rather than the usual `me merge(...)`. If MIR
  resolves methods by the `me` form, this declaration is invisible to it.
- `src/compiler/30.types/dim_constraints.spl:16` carries a comment about a
  former `e1.span.merge(e2.span)` having bound diagnostics incorrectly.

## How it was reached

This is the wall immediately after the ANY-escape absent-declared-type trap class
was closed (`820d2ea97b9`). Before that fix the build never got past semantic
analysis. See
`doc/08_tracking/bug/native_build_entry_closure_undefined_field_kind_2026-08-21.md`.

## Repro

```
SIMPLE_CACHE_SCOPE=mcp /mnt/data/seedperf/simple.mcpdbg native-build \
  --runtime-bundle core-c-bootstrap --source src/app --entry-closure \
  --entry src/app/simple_lsp_mcp/main.spl --strip --threads 2 \
  --output build/mcp-sanity/simple_lsp_mcp_server
```

~9 min on the LSP entry; use it rather than the MCP entry (~20-33 min).

## Resolution (2026-08-22)

Root cause: the desugar emits `x.merge(arr)` as a bare statement whose result is
discarded, and the pure-Simple MIR `Unresolved`-receiver arm only special-cased
`push` and `write_span`; `merge` fell through to the fail-closed const-0 error.

The "not a one-line fix" analysis above was wrong on one fact: the C runtime
ALREADY has the in-place extend — `rt_array_extend_i64(dst, src, count)` in
`src/runtime/runtime_native.c` (count < 0 = all), the exact primitive the Rust
seed's MIR uses for its `"merge" | "concat" | "extend"` arm
(`src/compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs`). It was
merely undeclared in `runtime.h` and in the LLVM backend's extern tables.

Fix (additive only):
- `50.mir/_MirLoweringExpr/method_calls_literals.spl`: new
  `lower_unresolved_array_merge` (mirror of `lower_unresolved_array_push`)
  emitting `rt_array_extend_i64(recv, other, -1)` plus the same
  `emit_method_writeback`; wired at both `push` dispatch sites. Seed parity:
  in-place extend through the stable handle, not `rt_array_concat` (a fresh
  array would be dropped by the statement form).
- `70.backend/backend/{llvm_backend,llvm_backend_tools,llvm_lib_translate,
  _MirToLlvm/asm_constraints_helpers}.spl` + `src/runtime/runtime.h`:
  declarations for `rt_array_extend_i64`.
- `80.driver/driver_build/incremental.spl:449`: a pattern-bound local named
  `hash_text` was resolved by the seed interpreter to the prelude FUNCTION
  `std.io_runtime.hash_text`, so every native-build that loaded a populated
  `build_cache.sdn` died with `method replace not found on type function`.
  Renamed the local (origin/main fixed the same line concurrently as `parsed_hash`; that version is kept). (Seed name-resolution defect; the rename is the
  pure-Simple-side fix.)

Spec: `test/02_integration/compiler/mir/array_concat_assign_merge_native_spec.spl`
(+ probe `probe_array_concat_assign_merge.spl`) — native-build + run, dual-run
identical to the interpret lane for int/text/struct arrays and `+=`. Fails
pre-fix with exactly `unresolved method call: merge`.

Not covered here: `val t = xs` alias before the concat — the array-copy loop it
lowers to hits a separate pre-existing llc SSA error, filed as
`llvm_text_backend_array_copy_loop_ssa_redefinition_2026-08-22.md`. Sibling
unresolved names `partition`, `new`, `upper` remain open.
