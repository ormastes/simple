# JIT lowering: nested fn inside impl method unresolvable ("Unknown variable: clamp_f")

Date: 2026-07-02
Status: fixed 2026-11-13 (seed HIR lowering; workaround left in place)
Severity: P3 (silent fallback to interpreter — large perf cliff)
Related: doc/03_plan/ui/production_readiness_master_plan_2026-07-02.md (W5)

## Symptom

Every program importing the 2D engine color path fails JIT compilation and
silently falls back to the interpreter:

```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering
error: Unknown variable: clamp_f while lowering EngineColor.to_rgba8
```

`clamp_f` resolves fine in interpreter mode. Root cause: `clamp_f` was a
**nested `fn` defined inside `to_rgba8` within an `impl` block** — HIR
lowering does not register nested fns in method bodies, so any nested-fn
call site fails JIT for the whole program. General bug: applies to every
nested fn inside an impl method, not just this one.

## Workaround

Hoisted the helper to module level as `_clamp_channel` in
`src/lib/common/engine/color.spl` (2026-07-02).

## Impact

All game2d examples (breakout, asteroids, pool, ...) and anything using
`EngineColor` run interpreted. Measured cost: one 800x600 breakout frame
takes >60 s interpreted; the W5 "60 s automated play session" gate is
unreachable until JIT works or the interpreter path gets much faster.

## Repro (verified 2026-07-02)

```bash
env SIMPLE_GAME_HEADLESS=1 bin/simple run examples/11_advanced/game2d/breakout/main.spl 2>&1 | grep clamp_f
```

## Resolution (2026-11-13)

Two separate defects, fixed at different times:

1. **Nested fn dropped by HIR lowering** (the reported `Unknown variable:
   clamp_f`). Fixed by `28286aa4f03` (2026-09-19, "fix(hir): lower a nested fn
   as a local closure instead of dropping it"). The `Node::Function` arm of
   `src/compiler_rust/compiler/src/hir/lower/stmt_lowering.rs` lowers a nested
   fn as `val <name> = \<params>: <body>`. Methods and free functions share
   that path: `lower_function` -> `lower_block`. At base `fe46f3430ac`, an
   exact replica of the pre-hoist `EngineColor.to_rgba8` (from `e66eff434bb`)
   already lowers, JIT-compiles and returns the right value.
2. **A nested fn calling another nested fn still fell back** (in a method AND
   in a free function). HIR types a lambda as its body type, not as a
   `HirType::Function`. Inside the second fn's outlined body, the first fn is a
   *capture*, which the intraprocedural `propagate_closure_call_types` cannot
   see. So the call boundary stayed `ANY`, and `compile_module` refused it with:
   `function 'P.combo' creates a lambda/closure the JIT closure ABI cannot
   compile (the call boundary types [TypeId(5)] -> TypeId(14) are not
   carryable ...)`. Fix: when the nested fn is fully annotated (every param
   typed, return type declared, no generics, no variadics), the synthesized
   `let` gets the declared `fn(P..) -> R` type. The binding and every capture
   of it then carry a real function type, and `function_signature_for_callee`
   returns the declared signature.

Still on the interpreter, by design: a **self-recursive** nested fn (HIR
closures have no letrec, so the guard in that arm keeps the fallback), mutual
recursion, and nested fns that are not fully annotated, generic or variadic
(those keep the old untyped binding).

### Evidence

Test: `src/compiler_rust/compiler/tests/nested_fn_in_method_jit.rs`. Each
case asserts that `hir::lower`, `mir::lower_to_mir` and JIT `compile_module`
all return `Ok` (any `Err` there is what triggers the interpreter fallback),
then checks the value `main` returns under the JIT.

| test | base `fe46f3430ac` | with fix |
|---|---|---|
| nested_fn_inside_impl_method_runs_under_jit | ok | ok |
| nested_fn_inside_class_method_runs_under_jit | ok | ok |
| original_engine_color_to_rgba8_shape_runs_under_jit | ok | ok |
| nested_fn_calling_nested_fn_inside_method_runs_under_jit | FAILED (closure ABI, ANY) | ok |
| nested_fn_inside_free_function_runs_under_jit | FAILED (closure ABI, ANY) | ok |

`cargo test -p simple-compiler --lib hir::`: 491 passed / 3 failed, both
before and after the fix, with identical failure names (pre-existing:
`existing_some_function_payload_keeps_its_function_binding`,
`result_optional_projection_and_explicit_patterns_still_lower`,
`lenient_lowering_records_dropped_list_comprehension`). The `mir:: codegen::
compilability` lib tests: 1719 passed / 1 failed, and that failure
(`primitive_field_method_call_is_builtin_qualified`) also fails at base. The
closure-related integration suites all pass: fn_ref_value_jit,
block_tail_coercion_jit, captured_local_write_is_compile_error,
entry_closure_defects_{jit,x86_64_none}, fn_value_followups_native,
imported_fn_value_native, placeholder_lambda_fn_param_jit,
interpreter_shared_empty_captured_env and
baremetal_entry_closure_imported_class_x86_64_none.

The `_clamp_channel` hoist in `src/lib/common/engine/color.spl` is left in
place on purpose.
