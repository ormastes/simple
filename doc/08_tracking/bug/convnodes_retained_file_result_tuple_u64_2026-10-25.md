# convnodes: nil payload in convert_flat_pattern; Result tuple slots u64/[u8]

Run-27e Phase 3 failures (no object for the modules below).

1. `compiler.frontend._FlatAstBridge.convert_nodes` (convert_nodes.spl:1672):
   `PatternKind.Array(arr_pat_elems, nil)` -> MIR "nil outside unsafe into optional
   payload slot (declared 'text?'); use None". Fixed: `None`. Permanent source fix.
2. `lib.nogc_sync_mut.io.retained_file`: `_retained_metadata -> Result<(u64, [u8]), text>`
   -> MIR "unsupported Result tuple payload element type" (slot 0 u64, then slot 1 array).
   `result_try_tuple_field_type` (50.mir/_MirLoweringExpr/result_tuple_payload.spl)
   admits only i64/bool/f64/text/tuple/record/unsized-array of admitted elements.
   Same class as resopt_result_optional_tuple_unwrap_2026-10-25.md.
   Workaround (@workaround in source): return a `RetainedMeta` record instead of a tuple.
   Open compiler bug: admit u64 (and u8 arrays) in Result tuple slots.

## Trap: decorator placement
`@unsafe(...)` attaches to the next item. Inserting a struct between the decorator
and `fn _retained_metadata` moved @unsafe onto the struct and left the fn without
it. Put new declarations ABOVE the decorator.

Also swept every `else: nil` into an `Expr?` slot and `defer_return_replay(nil, ...)`
in convert_nodes.spl to `None`.
