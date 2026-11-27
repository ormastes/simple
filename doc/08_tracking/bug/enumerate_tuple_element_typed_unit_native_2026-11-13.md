# `for (i, x) in xs.enumerate()` types `x` as unit in the native lane

- Status: OPEN (workaround at the one known site). Severity P2.
- Found: 2026-11-13, Windows Phase 2 compiler (frozen sha256 `c5c28bb7149f…`,
  pin `19c5aea975e5`) building the Phase 4 MCP server.
- Component: pure-Simple HIR/MIR typing of tuple destructuring over
  `enumerate()`; LLVM emission.

## Symptom

```
llc: module.ll:1585:33: error: void type only allowed for function results
  %l41 = call i64 @rt_native_eq(void %l35, ptr %l40)
```

in `lib.common.debug.service_v1.DebugServiceV1._reclaim_terminal_probe`, from

```simple
for (idx, probe) in self.probes.enumerate():
    if probe.state != DebugProbeStateV1.Applied:
```

The loaded field `probe.state` is emitted with type `void`: the destructured
tuple element `probe` (element type `DebugProbeV1`) is typed as unit, so its
field read and the `!=` operand lose their type. Indexing the same array
(`self.probes[idx].state`, line 451 of the same file) compiles.

## Workaround

`service_v1.spl` `_reclaim_terminal_probe` uses an indexed `while` loop,
linked to this record. Restore the `enumerate()` form when fixed.

## Fix needed

Type the tuple pattern elements of `for (a, b) in xs.enumerate()` from the
element type of `xs` (`(i64, T)`), in HIR, so MIR/LLVM never see a unit-typed
`b`. Add a native regression spec (a field read + enum comparison on `b`).

## Second form (2026-11-13)

Same class through a lambda parameter: `self.probes.filter(\probe: ... probe.state == DebugProbeStateV1.Applied)`
lowered `service_v1.__lambda_lift_2` with `rt_native_eq(void ...)`. `receipts_for`/`probes_for`
now use indexed loops, linked to this record; restore `.filter` with the owner fix.

## Fix (2026-11-13)

Root cause (pure-Simple HIR lowering, `src/compiler/20.hir/hir_lowering/`):

- `statements.spl` `StmtKind.For` tuple-destructuring arm: the binders of
  `for (a, b) in it:` received a declared type only when the iterable was a
  typed `Dict<K, V>`; for `xs.enumerate()` both binders were defined with no
  type and their `Let __elem[i]` stayed untyped, so MIR gave `b` a unit slot.
- `_Expressions/expression_core.spl` `ExprKind.Lambda` arm: an unannotated
  lambda parameter was always `HirTypeKind.Infer(0, 0)`; nothing carried the
  receiver's element type from `[T].filter(...)` into the lambda.

Fix:

- `statements.spl`: new `binding_receiver_element_type` (settled `T` of a
  `[T]`/slice receiver, from a typed binding or a declared field such as
  `self.probes`). The For tuple arm types `(i, x) in xs.enumerate()` as
  `(i64, T)` through the same declared-binder slots the Dict case uses.
- `types.spl`: `HirLowering.lambda_param_hint` (Error = none).
  `lambda_element_hint_for_method` / `stage_lambda_param_hint` stage `T`
  for a lambda-literal argument of an element-wise array method (`filter`,
  `map`, `any`, `all`, `find`, `each`, ...) in both MethodCall arms of
  `expression_core.spl`; the Lambda arm consumes it (and clears it) for a
  single unannotated parameter. Annotated params and non-array receivers
  are unchanged.
- Spec: `test/01_unit/compiler/20.hir/bootstrap_regressions/enumerate_lambda_element_type_spec.spl`
  lowers source through `HirLowering.lower_module` and checks the binder
  `Let` types and the lambda `HirParam.type_`.

Restoring the `enumerate()` / `.filter` forms in
`src/lib/common/debug/service_v1.spl` (`_reclaim_terminal_probe`,
`receipts_for`, `probes_for`) waits for a rebuilt Phase 2 compiler that
contains this fix; until then the indexed-loop workarounds stay.

Evidence (Rust seed `bin/simple.exe test`, which interprets the pure-Simple
HIR lowering): on unpatched `origin/release/1.0.0` the spec is 1 passed /
3 failed (`expected [infer, infer] to equal [int, named]`, lambda
`expected infer to equal named`); with the fix 4 passed / 0 failed.
