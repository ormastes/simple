# Pure-Simple `run` path: the HIR interpreter it reaches has no loop/match/return arms

**Date:** 2026-08-28  **Status:** OPEN (hand-off to compiler/backend owner)
**Found by:** perf_interp profiling lane (release/2026-08-27 tip `bb87306b64c`)

## Path

```
simple run <file>   (self-hosted full CLI)
  -> src/app/io/_CliCommands/run_commands.spl:107  cli_run_file
  -> src/compiler/80.driver/driver_api_interpret.spl:30  interpret_file
  -> src/compiler/80.driver/driver.spl:94-127  interpret() -> InterpreterBackendImpl.interpret_hir_module
  -> src/compiler/70.backend/backend/interpreter.spl / interpreter_expr.spl / interpreter_calls.spl
```

## Defect

`InterpreterBackendImpl.eval_expr` (`70.backend/backend/interpreter_expr.spl:18-414 (catch-all at :414)`)
has arms for literals, Var/NamedVar, ArrayLit/ArrayRepeat/TupleLit/DictLit, Index,
Binary/Unary, If/IfChain, Call, MethodCall (Static/Instance/FreeFunction only),
StaticCall, Lambda, HostGpuLane, NilLit/UnitLit — and then

```
case _:
    itrace("[EE] catch-all arm")
    Err(BackendError.not_implemented("expression kind not implemented"))
```

There is **no arm for `HirExprKind.While`** (`20.hir/hir_definitions.spl:580`),
nor for `For`, `Loop`, `Match`, `Return`, `Break`, `Continue`
(`/usr/bin/grep -rn "HirExprKind.While\|HirExprKind.For\|HirExprKind.Match\|HirExprKind.Return" src/compiler/70.backend/backend/` returns nothing).
Statements cover only `Let`, `Assign`, `Expr`, `Block` (`interpreter.spl:284-370`).
`MethodResolution.TraitMethod` returns `not_implemented`, and there is no
builtin-type method dispatch (`arr.push`, `d.keys()`, `s.len()` — no `"push"`/`"keys"`/`"len"`
strings anywhere in `interpreter*.spl`), so any program with a loop, a `match`,
an explicit `return`, or a collection method call fails with
`expression kind not implemented` / `unresolved method call`.

The file's own header (`interpreter.spl:1-5`) says:
"For runtime (interpreter mode), use compiler.core.interpreter instead." — but
nothing wires `compiler.core.interpreter` (`10.frontend/core/interpreter/mod.spl:192 core_interpret`)
into `interpret_file`; its only callers are its own `test_interp.spl`.

## Consequence

A pure-Simple full-CLI binary cannot execute a real `.spl` program through `run`.
This is consistent with the existing workarounds in the tree:
`run_commands.spl:214` ("Use Rust SFFI test runner directly (interpret_file path fails in native binaries)")
and `src/app/run/main.spl:delegate_run` re-spawning `./bin/simple run` (the Rust seed sibling).

## Reproduce

Needs a pure-Simple binary that exposes `run` or an `interpret_file` wrapper
(the tracked stage binaries expose only `compile`/`native-build`). Static proof above
suffices; a 3-line `while` program is the minimal fixture.

## Fix direction (not done here — outside the perf lane's directory scope)

Either (a) implement While/For/Match/Return/Break/Continue + builtin-type method
dispatch in `70.backend/backend/interpreter_expr.spl`, or (b) route `interpret_file`
to `compiler.core.interpreter.core_interpret`, which does implement them
(`eval.spl:695 eval_for_expr`, `:804 eval_while_expr`, `:848 eval_match_expr`,
`_EvalOps/call_method_eval.spl:931 eval_array_method`). Option (b) is what the
backend file's own header prescribes.
