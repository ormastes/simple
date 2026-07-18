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

## Audit (S71) — 2026-07-18

**Status:** CRITICAL — ALL 24 Dict-returning functions in the pure-Simple
compiler source are AT-RISK. All have `TryOperator` triggers; 8 have
`PatternMatch`; 6 have `AsyncAwait`. At least one (`process_async()`) is
bootstrap-critical. This is not a whack-a-mole issue — it's a categorical gap
affecting the entire class of composite-return codepaths.

### Findings

**Inventory Summary:**
```
Total Dict<T>/Map-returning functions in src/compiler/: 24
All 24 have TryOperator (.?) triggers in function bodies (50-line scan)
  - 8 also have PatternMatch (match keyword)
  - 6 also have AsyncAwait (async keyword)
Safe (no triggers): 0
AT-RISK (via other FallbackReasons): 24/24
```

**Complete AT-RISK Inventory:**

| File | Line | Function | Triggers |
|------|------|----------|----------|
| src/compiler/00.common/effects.spl | 184 | `init_builtins()` | TryOp, AsyncAwait |
| src/compiler/20.hir/hir_lowering/_Items/lowering_helpers.spl | 79 | `module_functions_destructure()` | TryOp |
| src/compiler/30.types/type_system/effects.spl | 127 | `build_effect_env()` | TryOp, AsyncAwait |
| src/compiler/30.types/type_system/effects.spl | 141 | `infer_mutual_effects()` | TryOp, AsyncAwait |
| src/compiler/30.types/type_system/effects.spl | 171 | `propagate_effects_transitive()` | TryOp, AsyncAwait |
| src/compiler/30.types/type_system/_StmtCheck/bindings_check.spl | 311 | `bind_pattern()` | PatternMatch, TryOp |
| src/compiler/40.mono/monomorphize_integration.spl | 68 | `process_modules()` | TryOp |
| src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl | 1709 | `snapshot_lambda_capture()` | PatternMatch, TryOp |
| src/compiler/60.mir_opt/mir_opt/collection_opt_core.spl | 463 | `local_use_counts()` | PatternMatch, TryOp |
| src/compiler/60.mir_opt/mir_opt/loop_detect.spl | 155 | `reachable_from()` | TryOp |
| src/compiler/60.mir_opt/mir_opt/loop_detect.spl | 176 | `can_reach_target()` | TryOp |
| src/compiler/70.backend/backend_types.spl | 365 | `as_dict()` | PatternMatch, TryOp |
| src/compiler/70.backend/backend/env.spl | 65 | `empty_env_scope()` | PatternMatch, TryOp |
| src/compiler/70.backend/backend/env.spl | 118 | `snapshot_locals()` | TryOp |
| src/compiler/70.backend/backend/cranelift_codegen_adapter.spl | 271 | `declare_module_statics()` | TryOp |
| src/compiler/70.backend/backend/_VhdlProcess/process_codegen.spl | 336 | `mark_return_chain_handled()` | PatternMatch, TryOp |
| src/compiler/70.backend/backend/_VhdlProcess/process_codegen.spl | 348 | (unnamed) | PatternMatch, TryOp |
| src/compiler/80.driver/driver_pipeline.spl | 257 | `process_async()` | TryOp, AsyncAwait |
| src/compiler/90.tools/async_integration.spl | 320 | `process_async_mir()` | TryOp, AsyncAwait |
| src/compiler/90.tools/coupling/metrics.spl | 18 | `compute_fan_out()` | TryOp |
| src/compiler/90.tools/coupling/metrics.spl | 24 | `compute_fan_in()` | TryOp |
| src/compiler/90.tools/lint/_LintMain/config_and_model.spl | 92 | `build_default_levels()` | TryOp |
| src/compiler/90.tools/lint/_LintMain/config_and_model.spl | 153 | `profile_default_levels()` | PatternMatch, TryOp |
| src/compiler/99.loader/jit_context.spl | 62 | `type_registry()` | TryOp |

### Bootstrap-Critical Path Status

- `process_async()` (driver_pipeline.spl:257) is called during the compilation
  driver's MIR processing phase (confirmed: compiler/80.driver/driver_pipeline.spl:166,
  compiler/80.driver/driver.spl:1084). This function returns
  `Dict<text, AsyncStateMachine>` with TryOp + AsyncAwait triggers.
- If native `--backend=cranelift` codegen encounters any of these functions via
  PatternMatch, Closure, or other non-CollectionLiteral fallback reasons, the
  corrupted boxed result will propagate as garbage handles into native consumers.
- Risk is **active on bootstrap path**, not hypothetical: `process_async()` is
  invoked unconditionally during driver setup.

### Fix Mechanism Sketch

**Current state (broken):**
1. `compile_interp_call()` in src/compiler_rust/compiler/src/codegen/instr/core.rs
   (~line 758–839) calls `rt_interp_call()` to invoke the interpreter, receiving
   a `RuntimeValue` (NaN-boxed u64).
2. For composite returns (Dict, Array, Option), lines 826–835 use heuristic
   checks: if `keep_boxed_result || interp_call_keeps_boxed_result(func_name)`,
   store the boxed wrapper directly (line 834). Otherwise, for non-F64,
   non-extern-bridge destinations, there is no unboxing step — the wrapped
   `RuntimeValue` is stored as-is.
3. Downstream native code (e.g., `Dict.len()`) expects a tagged heap handle
   (pointer + type tag in the u64), not a NaN-boxed wrapper, and reads garbage.

**Required fix:**
- Extend `runtime/src/value/sffi/value_ops.rs` with a new function (e.g.,
  `rt_value_as_handle`) that extracts the tagged heap pointer from a
  `RuntimeValue` NaN-box without stripping the tag.
  - Input: `RuntimeValue` (u64 in NaN-box format, tag in high bits per tags.rs)
  - Output: i64 (the same tagged handle, usable by runtime Dict/Array/Option ops)
  - Mechanism: RuntimeValue::is_heap() checks the tag; if true, extract the
    payload (lower 48 bits) and preserve the tag (upper bits).
- Wire this into `compile_interp_call()`: when `!keep_boxed_result` and the
  destination type is a user-defined composite (Dict, [T], Option<T>, class),
  call `rt_value_as_handle` instead of leaving the boxed wrapper.
- Add runtime_sffi.rs entry for the function (per runtime_symbols.rs pattern).
- Regression test: a Dict-returning function with TryOp/PatternMatch should
  round-trip through InterpCall with correct handles.

### Risk Assessment

**Scope:** The gap affects any pure-Simple function with composite return type
that is forced through InterpCall for any FallbackReason. The S68 dict-literal
fix removed *one* reason; 23 others remain (PatternMatch, TryOp, etc.).

**Severity:** Silent wrong result (handles read as garbage), affecting any
bootstrap that routes a Dict-returning function through the interp path and
then calls methods on the result.

**Recommendation:** Implement the `rt_value_as_handle` fix before any major
bootstrap with dict-using functions on the native cranelift path. Track as
a critical pre-release blocker.

## Related

- `doc/08_tracking/bug/s59_cranelift_dict_return_abi_root_cause_2026-07-17.md`
- `doc/08_tracking/bug/seed_native_cranelift_dict_return_abi_2026-07-17.md`
- Fix landed alongside this doc: `compiler/src/compilability.rs` (`Expr::Dict`
  no longer adds `FallbackReason::CollectionLiteral`), plus regression tests in
  `compiler/src/compilability.rs` and `compiler/src/mir/hybrid.rs`.
