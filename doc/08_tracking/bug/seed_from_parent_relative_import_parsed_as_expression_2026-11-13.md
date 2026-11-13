# Seed parses `from ..pkg import {...}` as an expression: `variable 'from' not found`

Date: 2026-11-13. Status: FIXED (seed parser gate + `src/app/interpreter` migrated to `use`).

## Symptom

Importing any module of `src/app/interpreter` that used a parent-relative Python-style
import failed on the Rust seed:

```
error: semantic: variable `from` not found
```

First reported as a leftover of `fault_detection_module_missing_2026-11-13.md` (PR #8768):
`call/function_exec.spl` and `control/control/loops.spl` could not be load-tested.

## Root cause

`from` is a soft keyword. The seed's statement gate
(`src/compiler_rust/parser/src/parser_impl/core.rs`, `TokenKind::From` arm) routes to
`parse_from_import` only when the next token is `Identifier | Match | Mod | Shared | Dot`.
`..` lexes as `DoubleDot` and `...` as `Ellipsis`, so `from ..core import {A}` fell through
to `parse_expression_or_assignment`: `from` became an identifier expression and
`import {A}` a second statement. `parse_module_path` itself already handled both tokens.

The tell in the diagnostics: the broken line warns `Deprecated: 'import' keyword` at the
column of `import`, while a working `from sibling import {...}` warns
`Deprecated: 'from ... import' syntax` at column 1.

Forms, measured on the seed:

| form | before |
|---|---|
| `from std.common.x import {...}` (absolute) | loads |
| `from sibling import {...}`, multi-line braces | loads |
| `from .sibling import {...}` | loads |
| `from ..pkg import {...}`, `from ..pkg.mod import {...}` | `variable 'from' not found` |

The pure-Simple parser has no such gap: `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl`
handles `from` at module level with explicit `...` / `..` / `.` prefixes.

## Fix

1. Seed gate: `DoubleDot` and `Ellipsis` added to the `from` statement gate. The form is
   deprecated but accepted, and the pure-Simple parser accepts it, so the seed must not
   mis-parse it silently.
2. `src/app/interpreter`: all 156 `from X import {...}` lines in 60 files rewritten to the
   canonical absolute `use app.interpreter.<pkg>.{...}` form. The gate fix alone would not
   have been enough: the deployed seed is unchanged until redeploy, the seed itself marks the
   form deprecated in favour of `use`, and several relative paths were wrong for the real
   layout (`control/control/loops.spl` used `..core`, which is `control/core`;
   `call/arg_binding.spl` used `..control.match`, which lives in `control/control/`;
   `core/eval.spl` used `..control`, which has no `__init__.spl`). Each path was resolved
   against the directory tree, not rewritten textually.

## Evidence

Minimal repro (three files: `pkg/core.spl`, `pkg/call/user.spl` with
`from ..core import {answer}`, `main.spl`):

- deployed seed: `error: semantic: variable `from` not found`, rc=1
- seed built from this change: prints `84`, rc=0; the four specs below also pass on it

Seed parser unit tests (`cargo test -p simple-parser`):

- `test_parent_relative_from_import_is_one_use_statement`: red without the gate change
  (`"from ..core import {Interpreter, Value}\n" must be one statement`), green with it.
- `test_from_stays_an_identifier_when_not_an_import`: `from = 3`, `val from = 1`, `from(1)`
  still parse as non-imports.
- Whole crate, with vs without the gate change: the failing set differs only by the new
  test. Five other tests fail on both sides (`test_python_def_detection`,
  `test_danger_block_is_unsafe_boundary_not_call`,
  `unsafe_block_is_valid_in_value_position_and_calls_stay_calls`,
  `stage2_failure_consumers_parse_strictly`, `test_multiple_decorators`).

Specs on the deployed seed (migration only):

| spec | before | after |
|---|---|---|
| `test/01_unit/app/interpreter/call_function_exec_load_spec.spl` | `outcome=ERROR executed=0` (commit `18484e9a883`) | `outcome=OK passed=9 failed=0` |
| `test/01_unit/app/interpreter/control_loops_load_spec.spl` | `outcome=ERROR executed=0` | `outcome=OK passed=10 failed=0` |
| `test/01_unit/lib/common/fault_detection_spec.spl` | 11/11 | 11/11 |
| `test/01_unit/lib/nogc_async_mut_noalloc/execution/watchdog_manager_spec.spl` | 4/4 | 4/4 |
| `test/01_unit/app/interpreter/env_ffi_optional_decl_spec.spl` | not run | 1/1 |

The two load specs declare 2 and 3 examples; the extra 7 are `core/environment_spec.spl`
and `core/value_spec.spl`, which the seed picks up when it loads the `core` package
directory. Pre-existing behaviour, not changed here.

No statement starting with `from ..` that is not an import exists in `src`, `test` or
`examples`, and after the migration no `from ..` import remains either.

## Left over

- `src/app/interpreter` is not live. Nothing outside the tree imports it; only specs do.
  `src/compiler/10.frontend/core/interpreter/mod.spl` lists it as the legacy interpreter,
  deleted 2026-02-10; it was restored by `ef94628696b`.
- Loading is lazy about names. Five imports point at modules that do not exist anywhere
  (`shared.pattern` x2 in `control/control/match.spl`, `shared.operators` x2 in
  `expr/arithmetic.spl`, `shared.contracts` in `core/contract.spl`) and were kept as
  `use shared.<mod>.{...}`. Some imported names are not exported by their target
  (`Closure` from `core`, `eval_control` from `control.control`; `eval_control` is defined nowhere).
  The modules load; calling into those paths is untested and expected to fail.
- `expr/calls.spl` imported `ffi.debug`; the functions live in `std.sffi.debug`, now used.
- The deployed seed still has the gate gap until the next seed redeploy.
- 79 deprecated `from X import` lines remain elsewhere under `src`, `test` and `examples`
  (78 bare, 1 `.sibling`); both forms parse on the seed.
