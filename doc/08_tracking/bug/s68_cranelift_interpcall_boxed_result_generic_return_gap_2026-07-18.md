# Follow-up: seed cranelift InterpCall boxed-result gap for generic/composite return types

**Date:** 2026-07-18
**Lane:** S68
**Status:** OPEN — documented as a follow-up, NOT fixed here (out of scope for the
Dict-literal fix landed alongside this doc; risky, needs its own verification).
**Severity:** P2 (silent wrong result), seed `--native --backend=cranelift` path only.

## Context

Lane S68 root-caused and fixed
`doc/08_tracking/bug/s59_cranelift_dict_return_abi_root_cause_2026-07-17.md`:
`Expr::Dict` literals unconditionally added `FallbackReason::CollectionLiteral`
in `compiler/src/compilability.rs`, forcing every *caller* of a Dict-returning
function through `MirInst::InterpCall` (the hybrid interpreter-bridge call).
That fix removed the Dict-literal-specific trigger — Dict literals now stay on
the native path exactly like the already-fixed Array/Tuple literals.

That fix does **not** close the underlying mechanism. It only removes one of
several possible reasons a function can be forced through `InterpCall`.

## The residual gap

`compile_interp_call` in `compiler/src/codegen/instr/core.rs` (~line 758-839)
decides how to convert the interpreter's boxed `RuntimeValue` result back to a
native value:

```rust
let is_extern_bridge = func_name.starts_with("rt_") || func_name.starts_with("spl_");
let keep_boxed_result = boxed_result || interp_call_keeps_boxed_result(func_name);
let value = if !keep_boxed_result && (... f64 ...) {
    call_runtime_1(ctx, builder, "rt_value_as_float", result)
} else if !keep_boxed_result && (is_extern_bridge || vreg_is_native_equality_scalar(ctx, *d)) {
    call_runtime_1(ctx, builder, "rt_value_raw_i64", result)
} else {
    result   // <-- stays as the interpreter's boxed RuntimeValue
};
```

For a **plain user-defined function** (not `rt_`/`spl_` prefixed) whose call
destination vreg has no recognized scalar type (the common case for
Dict/Array/struct/Option returns — comment in `compilability.rs::return_type_keeps_boxed`
confirms "Call dests carry no entry in vreg_types" for these), execution falls
to the final `else` branch: the interpreter's boxed `RuntimeValue` wrapper is
stored into the vreg **unconverted**. Downstream native consumers (e.g.
`Dict.len()`, `Dict.contains_key()`, native indexing) expect the runtime's
native tagged-pointer handle, not the interpreter's boxed wrapper, and read
garbage — this is exactly the S59/S68 symptom (`len()` = -1, etc.).

`return_type_keeps_boxed` (same file) is explicit that this is a known,
deliberate scope boundary, not an oversight:

> Conservative on purpose: only unambiguous heap composites — tuples and
> `text` — are flipped to boxed. ... **Arrays, options, and generics are left
> as a future extension** once each has a verified round-trip.

So: **any** function returning `Dict`, `[T]`/Array, `Option<T>`, or a
user-defined composite type that is forced through `InterpCall` for *any*
`FallbackReason` other than the now-fixed `CollectionLiteral` (e.g.
`PatternMatch`, `Closure`, `TryOperator`, `ActorOps`, `UserMacros`,
`DynamicTypes`, ...) will hit this same corruption. The S68 fix only closed
the Dict-literal-specific door; the room is still open.

## Blast-radius check (pure-Simple compiler source)

```
$ grep -rn '\-> *Dict<\|\-> *Map<' src/compiler/ | wc -l
23   (across 17 files)
```

Representative hits: `src/compiler/00.common/effects.spl:184` (`init_builtins`),
`src/compiler/20.hir/hir_lowering/_Items/lowering_helpers.spl:79`
(`module_functions_destructure`), `src/compiler/30.types/type_system/effects.spl`
(3 functions), `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl:271`
(`declare_module_statics`), `src/compiler/90.tools/lint/_LintMain/config_and_model.spl`
(2 functions), and 11 more (full list reproducible with the grep above).

None of these were individually audited here for whether their *bodies* (or
their transitive callees) trip a *different* `FallbackReason`. That audit —
checking each of the 23 sites (and their callers, since the corruption
manifests at the call site, not the callee) for pattern-match/closure/try-op/
actor/macro usage that would still route them through `InterpCall` — is the
concrete next step before this class of bug can be called fully closed for the
bootstrap-relevant cranelift path.

## Recommended next step

Two independent, non-mutually-exclusive paths, same as the original S59 doc's
options A/B applied at the right layer:

1. **Keep shrinking the false-fallback surface** (the S68 approach): audit each
   remaining `FallbackReason` producer in `compilability.rs` the same way Dict
   was just audited — is it still type-blind/overly-conservative for
   constructs that already lower to native MIR? Each one removed shrinks the
   set of functions that can ever reach the broken `InterpCall` path.
2. **Fix the bridge itself**: extend `compile_interp_call` / `return_type_keeps_boxed`
   so generic/composite return types (Dict, Array, Option, struct) get a
   correct **native-handle extraction** step analogous to `rt_value_raw_i64`/
   `rt_value_as_float` — i.e. a `rt_value_as_handle`-style unwrap that pulls
   the tagged heap pointer out of the interpreter's boxed `RuntimeValue`
   instead of either leaving it boxed (current default) or blindly truncating
   it (which the doc explicitly warns against for tuple/text). This closes the
   gap at the source instead of playing whack-a-mole with fallback reasons.

## Related

- `doc/08_tracking/bug/s59_cranelift_dict_return_abi_root_cause_2026-07-17.md`
- `doc/08_tracking/bug/seed_native_cranelift_dict_return_abi_2026-07-17.md`
- Fix landed alongside this doc: `compiler/src/compilability.rs` (`Expr::Dict`
  no longer adds `FallbackReason::CollectionLiteral`), plus regression tests in
  `compiler/src/compilability.rs` and `compiler/src/mir/hybrid.rs`.
