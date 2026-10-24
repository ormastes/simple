# Cranelift verifier: `return ()` in a Unit-signature function (2026-10-24)

Status: OPEN (source workaround active; compiler fix committed, unverified)

## Symptom

Phase-3 native build (`build/phase3-ref/run-16/build.log:119962`), unit
`compiler.mir._MirLoweringExpr.expr_dispatch`:

```
cranelift: AOT define_function error: Verifier errors:
- inst70 (return v53): arguments of return must match function signature
```

The log names only the unit. The retained diagnostic dir
(`simple-aot-diagnostic-2e0017fe84ce`) is empty.

## Candidate (static analysis, no probe)

1. **`me emit_pending_finally_for_transfer() -> ():`**
   (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:3181`). It has
   `return ()` at :3195, in the function's first block (the nil guard), which
   fits a low `inst70`. This is the only `return <expr>` inside a unit or
   untyped function in this file, and the only `return ()` anywhere in
   `src/compiler`.
2. No other candidate. No `fn`/`me` without a return type contains a
   `return <value>`. A declared-return path that yields nothing would produce
   a bare `(return)`, not `(return v53)`. The file has no `-> f64/f32`
   functions, so this is not the float-erasure sibling
   (`cranelift_float_return_erased_to_i64_2026-10-24.md`).

## Root cause

- `lower_return_expr` (expr_dispatch.spl ~3091) always emits
  `Ret(Some(<lowered value>))` for `return <expr>`, even when the function's
  MIR signature return type is `Unit`.
- The implicit tail does handle `Unit`: `function_lowering.spl:802`
  terminates with `terminate_return(nil)`.
- The Cranelift adapter's `build_signature`
  (`70.backend/backend/cranelift_codegen_adapter.spl:328`) emits no result
  for a Unit signature. Its `Ret(value)` arm (:983) then emits
  `return v53`, so the arity does not match.

The type-erasure path was ruled out. If bootstrap HIR erasure had turned
`-> ()` into i64 (`declaration_lowering.spl:382-402`), the signature would
have an I64 result. A Unit temp also maps to `CL_TYPE_I64` (adapter :304), so
the verifier would accept it. The failure therefore needs a Unit signature
with a value return.

## Workaround (`simple-boot-adhoc` lane)

At expr_dispatch.spl:3195, `return ()` becomes `return`. The behaviour is the
same, because a bare return in a unit function already lowers to
`Ret(None)`. The line is tagged
`# @workaround bug=cranelift_unit_fn_return_unit_value_2026-10-24`.

## Compiler fix (`simple-p3fix-unitret`, based on simple-boot-p2shard HEAD)

- `lower_return_expr` now checks `current_mir_signature_returns_unit()`,
  which mirrors `build_signature`: Unit, and the function is not `main`. When
  it is true, the value is lowered for its side effects and the function
  takes the bare-return path.
- Regression spec:
  `test/01_unit/compiler/50.mir/unit_fn_return_unit_value_spec.spl`.
  Neither the spec nor the fix has been run, because the host is
  memory-constrained and no probes were allowed.

## Retirement

Remove the workaround only after a Stage 2 built with the compiler fix
compiles `expr_dispatch.spl` with `return ()` restored.
