# Native full CLI `test`/`run`: imported functions, interpolation, non-entry modules

Status: verification-pending
Date: 2026-11-15

## Symptom
The natively built full CLI (`build/nb/cli_tip.exe`, sha256 `0acd858ea52a5016...`)
fails every spec: `function 'describe' not found`. On this host the runner
also reports `TERM ... child died by signal` after ~92 s for
`test/01_unit/lib/io/windows_compare_object_handles_spec.spl`.

## Root cause
Native `run` and `test` (the spec child is `cli_tip.exe run ...`) go through
`interpret_file` -> `CompilerDriver.interpret_pipeline` -> the pure-Simple HIR
tree-walker `InterpreterBackendImpl` (`src/compiler/70.backend/backend/`).
`SIMPLE_EXECUTION_MODE=jit` is not honored by `run`. This walker had three gaps
that every spec hits:
1. **Imported functions never resolved.** `fn_by_name` was built from the entry
   module only. The provider modules were handed to the backend only for the
   ownership check, so any call into another module (`describe`, `it`,
   `expect` from `std.spec`) failed with `function '<name>' not found`.
2. **Every retained module was run as a program.** `interpret_pipeline` looped
   over all sources and required a `main` in each one, so the first import
   failed with `Interpret error in <dep>: module has no main function`.
3. **String interpolation was not evaluated.** The `StringLit` arm dropped the
   interpolation list, so `"sum={helper_add(2, 3)}"` printed verbatim.

## Fix
- `env.spl`/`interpreter.spl`/`interpreter_calls.spl`: build a `fn_owner`
  index (name -> provider module) once. On a local miss the callee runs in a
  context built for its own module (its own names map and fn index, the shared
  env). The entry module's own definitions always win.
- `driver.spl`: run only the entry module (`sources[0]`).
- `interpreter_expr.spl`: evaluate interpolation slots, using the same segment
  splitting as MIR's `split_interpolation_segments`.

Regression spec: `test/01_unit/compiler/backend/interpreter_backend_cross_module_spec.spl`.
RED: `expected string:sum={2 + 3}! to equal string:sum=5!`,
`expected error:function 'helper_add' not found to equal int:5`.
GREEN: `Results: 3 total, 3 passed, 0 failed`.

## Open (plan): std.spec still cannot run on this walker
The walker has no arms for most HIR kinds that std.spec and real specs use:
statements `Return`/`Break`/`Continue`/`While`/`For`/`Loop` are not covered
(stmts handled: Let, Assign, Expr, Block, AsmAssert). Expression kinds not
handled include `MatchCase`, `While`, `For`, `Loop`, `Return`, `Try`,
`OptionalChain`, `NullCoalesce`, `ExistsCheck`, `Unwrap`, `StructLit`,
`EnumLit`, `Cast`, `As`, `Range`, `Comprehension`, `TupleIndex`, `With`,
`TryCatch` and `TypeTest`. Module-level `val`/`var` of a provider are not
initialized. Interpolation `:format` specs are ignored. Each is its own slice.
The alternative is to route native `run`/`test` to a complete engine, such as
the MIR interpreter (`95.interp/mir_interpreter.spl`), which no CLI path
calls today.

## Perf (recorded, not fixed here)
`cli_tip.exe run` of a two-file program takes 48 s wall, while the HIR phase
reports `elapsed_ms=26`. The time goes elsewhere in startup or admission.
