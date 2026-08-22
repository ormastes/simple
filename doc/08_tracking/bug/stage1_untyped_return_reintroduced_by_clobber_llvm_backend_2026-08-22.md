# Stage1 fatal sweep: untyped-return fatal reintroduced by clobber; array_advanced in lowering set

**Date:** 2026-08-22  **Status:** RESOLVED (this change)  **Lane:** pure-Simple bug sweep

## Sweep result (run9 + fp2/fp5/fp6/fp7/fp8 logs)
All `[hir-fatal]` texts across the six stage1 logs normalize to five classes:

| class | count | example | status |
|---|---|---|---|
| `unresolved name/type` | ~390 | driver.spl `CodegenTarget` | owned by another lane |
| `enum payload dependency X conflicts` | 9 | driver*.spl `AdviceForm` | fixed on origin 83afe82f50a (requalify) |
| `untyped function returns a value` | 4 | incremental.spl, shadow_mode.spl | fixed f9a7b5cb296 |
| `generic functions are not supported ... (#158 Phase B)` | 2 | `lexer_array_len` | fixed d2bdc42d8ad |
| `eprint` unresolved on native path | — | — | fixed f858c7cf32e |

`[hir-payload-origin-unresolved]` lines are all builtin names (`text`/`i64`/`Option`/...) and belong to the owned unresolved class.

## Found ahead of run9 (static scan of the 667-module lowering set)
1. **`src/compiler/70.backend/backend/llvm_backend.spl:compile_module` lost its `-> Result<LlvmCompileResult, text>`.**
   f9a7b5cb296 added it; f858c7cf32e (the eprint fix) was a stale-snapshot clobber of this file and dropped it again.
   `scripts/check/check-untyped-return-value.shs` was RED on origin: 1 hard-scope offender + 4 stale gzip rows.
   Fix: annotation restored; baseline pruned. Pin: `test/01_unit/compiler/hir/llvm_backend_compile_module_typed_return_spec.spl`.
2. **`src/lib/*/array_advanced.spl`** (in run9's lowering set as `src/std/nogc_async_mut/array_advanced.spl`) carried 5 untyped
   value-returning fns (`array_group_consecutive`, `array_transpose`, `array_mode`, `array_median`, `array_index_of_subarray`)
   that were only ratcheted, because the hard scope listed `src/lib/*/array.spl` and not `array_advanced.spl`.
   Fix: typed in all three family copies; hard scope widened; shape added to `untyped_return_value_shapes_spec.spl` (errors pre-fix, clean post-fix).
3. Generic structs/classes/impls: none in the 667 set. Generic fns: only the 23 `hir_visitor.spl` walkers, already filed OPEN under #158 Phase B (baseline of `check-no-free-generic-fn-in-bootstrap-closure.shs`). They WILL fatal when run9 reaches `src/compiler/hir/generated/hir_visitor.spl`; do not work around in source.

## Notes
- Single-module `native-build` of llvm_backend.spl pulls a 375-module closure and exceeds 10 min at load 22; per-class native reproduce is not viable on this host, so reproduction is at the HIR-lowering unit level.
- The guard's static BFS closure (529) is smaller than run9's 667 (std/lib alias and symlink name variants); the scans above were run over run9's own module list.
