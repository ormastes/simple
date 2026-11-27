# Positional `t.N` on an `Any` receiver lowered to `rt_index_get` — native json values read as nil

- **Date:** 2026-11-13
- **Status:** FIXED (source; reaches native builds after the next Phase 2 rebuild)
- **Severity:** High — every `std.common.json.types` reader (`json_get_type`,
  `json_to_number`, ...) is broken in native builds; `json_to_number` then
  segfaults (rc 139)
- **Area:** `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`
  (`lower_index_expr`, `is_any_runtime_index_base`),
  `src/compiler/20.hir/hir_lowering/_Expressions/expression_core.spl`
  (positional-field desugar)
- **Follows:** `2026-11-13_cranelift_mcp_json_deep_clone_f64_call_abi.md` § Open

## Symptom

Frozen Windows Phase 2 (`build/diag-phase4/phase2.exe`), 4-module json fixture:
`json_get_type(json_number(2.5))` prints `null`, the runtime logs
`rejected invalid array handle before dereference; probable compiler/FFI ABI
mismatch`, and `json_to_number(n)` segfaults.

## It is not Cranelift-specific

Reduced fixture (no json import; `fn mk(v: f64): ("number", v)`,
`fn tag_of(v: any) -> text: v.0`), same frozen compiler, `THREADS=1`:

| backend | `tag_of(mk_int(7))` | `json_get_type(json_string("hi"))` | `tag_of(mk(2.5))` | `json_get_type(json_number(2.5))` |
|---|---|---|---|---|
| cranelift | empty | `null` | empty | `null` |
| llvm | empty | `null` | empty | `null` |

Both print the same runtime error. Int, text and f64 payloads all fail, so this
has nothing to do with f64 boxing. The tuple layout (`rt_alloc` block of N
words) is the same on both backends.

## Root cause

c69643f2a0e (2026-10-27) sends every index read on an `Any` runtime-value base
through `rt_index_get`, so that an unsafe `x[3]` on a byte-packed `[u8]` reads
correctly. HIR desugars positional `t.N` into the same
`Index(base, IntLit(N))` node, so `value.0` on `value: any` took that path
too. A native tuple is a raw `rt_alloc` block, not a registered
array/string/dict, so `rt_index_get` (`src/runtime/runtime_native.c`) returns
nil (3) for it. Before c69643f2a0e such a read was a native word load.

## Fix

- HIR: the synthesized positional index literal now carries the base's span.
  Before, it carried `e.span`, which is span id 0 (`expr_field_access` gets no
  real span).
- MIR: `index_is_tuple_positional(base, index)` (a literal index whose span
  equals a non-empty base span) keeps a positional read off the `rt_index_get` route,
  so it falls through to the native GEP+load path that erased-handle tuple
  reads already use. A source `x[N]` literal has its own token span, so
  c69643f2a0e's unsafe `x[3]` behaviour does not change. A synthesized node
  whose base and index both carry `Span.empty()` is never positional, so it
  stays on `rt_index_get`.

Regression: `test/01_unit/compiler/50.mir/any_index_read_spec.spl`, case
"keeps a positional t.0 read on an Any receiver a native tuple word load":
fails without the fix. Two direct-lowering cases cover the span rule: an Index
whose base and IntLit spans are both `Span.empty()` on an `Any` receiver still
calls `rt_index_get` (fails if the non-empty-span guard is removed: 7/8), and an
Index whose IntLit carries a non-empty base span does not. Full spec: 8/8. The
`x[3]` rt_index_get case still passes.

## Open

- Tuple destructure desugars (`lower_tuple_destructure`,
  `match_index_projection`) also emit `Index(base, IntLit)` with their own
  spans. On an `Any` base they still take `rt_index_get`.
- Under `SIMPLE_BOOTSTRAP=1` a non-tuple-typed base still goes through
  `rt_array_get`, which raw tuples do not satisfy either (behaviour from before
  c69643f2a0e, unchanged here).
- Native verification of the fixture needs a Phase 2 rebuild that carries this
  change.
