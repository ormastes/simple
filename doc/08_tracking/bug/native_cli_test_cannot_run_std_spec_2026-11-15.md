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
   module only. The backend received only `providers.modules` from
   `ownership_provider_index_v1`, which keeps nogc-strict modules alone, and
   used it just for the ownership check. Any call into another module (`describe`, `it`,
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
  `interpret_hir_module_with_live_providers` now takes the ownership
  providers and, separately, every retained module (`ctx.hir_modules`).
- `driver.spl`: run only the entry module (`sources[0]`).
- `interpreter_expr.spl`: evaluate interpolation slots, using the same segment
  splitting as MIR's `split_interpolation_segments`.

Regression spec: `test/01_unit/compiler/backend/interpreter_backend_cross_module_spec.spl`.
RED: `expected string:sum={2 + 3}! to equal string:sum=5!`,
`expected error:function 'helper_add' not found to equal int:5`.
GREEN: `Results: 3 total, 3 passed, 0 failed`.

## Native evidence (rebuilt `cli_tip.exe`, sha256 `690e5663d26a48f9...`)
Rebuilt with the K1 command in `full_cli_native_link_missing_symbols_2026-11-15.md`
(`Build complete: 4 compiled, 3709 cached, 0 failed`).
- Two-file program (`a.spl` prints `"sum={helper_add(2, 3)}"`, `helper_add` from `b.spl`):
  before `sum={helper_add(2, 3)}` then `Interpret error in build.nb.xm.b: module has no main function` (rc=1);
  after `sum=5` (rc=0).
- `cli_tip.exe run test/01_unit/lib/io/windows_compare_object_handles_spec.spl`
  now gets past `describe` and stops at the next walker gap (67 s wall):
  `Interpret error in test.01_unit.lib.io.windows_compare_object_handles_spec: unresolved method call: len`.
  So `test <spec>` still reports no passed examples. The brief's goal of
  nonzero passed was **not** reached.

## Slice 1 (2026-11-16): builtin methods, loops, return, literal match
`interpreter_control.spl` adds: Unresolved receiver methods dispatched on the
runtime value (text len/is_empty/trim/contains/starts_with/ends_with/split;
array len/is_empty/push (written back to the variable)/contains; dict
len/is_empty/keys/contains_key/has; int/bool to_text), dict indexing,
`While`/`Loop`/`For` (array, text, dict keys, bounded `Range`), `Return`/
`Break`/`Continue` (a `BackendErrorKind.ControlFlow` error; the return value
rides on `BackendError.ctl_value` because a value parked on the by-value
Environment is lost across copies), and `MatchCase` with wildcard/literal/
binding/or patterns plus guards. Spec:
`test/01_unit/compiler/backend/interpreter_backend_walker_slice1_spec.spl`.

Alternatives checked: `src/app/interpreter` (25k lines) has rotted: it imports
`parser.treesitter` / `lib.parser.parser`, which do not exist, and `run`
on it fails at parse in `core/__init__.spl:18`. The MIR interpreter keeps
values in i64 slots with placeholder `rt_array_*` stubs (lines 1114-1137) and
no text/dict model, so it is not a drop-in for std.spec either.

## Open (plan): remaining walker gaps
`TraitMethod` calls; expression kinds `Try`, `OptionalChain`, `NullCoalesce`,
`ExistsCheck`, `Unwrap`, `StructLit`, `EnumLit`, `Cast`, `As`,
`Comprehension`, `TupleIndex`, `With`, `TryCatch`, `TypeTest`; enum/struct/
tuple match patterns; open ranges; module-level `val`/`var` of a provider;
interpolation `:format` specs. Each is its own slice.

## Perf (recorded, not fixed here)
`cli_tip.exe run` of a two-file program takes 48 s wall, while the HIR phase
reports `elapsed_ms=26`. The time goes elsewhere in startup or admission.
`provider_context_for` also rebuilds the owner module's name map and fn index
on every cross-module call. A per-module context cache is the follow-up.

## 2026-11-16: `unresolved method call: len` (receiver kind function)

Not a stale cache (the only emitter is #9601's fallback in
`interpreter_control.spl`). Cause: the HIR interpreter never bound module-level
`val`/`var` (`HirModule.constants`), so a NamedVar read of an imported global
(`_aggregate_ledger_paths` at `src/lib/nogc_sync_mut/spec.spl:97`) fell back to
a Function value. Fixed by evaluating provider + entry constants as globals
before `main`; Array `push` now returns the grown array so `xs = xs.push(v)`
keeps xs. Native repro: `test/fixtures/native_interp_module_var/main.spl`
(RED `unresolved method call: push (receiver kind function)`, GREEN
`ledger_len=1`; seed interpreter was never affected).
Next blocker: `expression kind not implemented (disc 1572658204) at
src/lib/nogc_sync_mut/spec.spl:1244:21` (`env_get(...) ?? ""`). Status stays
verification-pending.
