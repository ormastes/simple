# Seed interpreter uses a unit-typed `main`'s tail value as the process exit code

**Filed:** 2026-11-16
**Severity:** high -- `simple test <spec>` exits 1 on a fully green spec
**Status:** verification-pending

## Symptom
Tip seed `simple.exe test <spec>` prints `Results: N total, N passed, 0 failed`
yet exits 1 ("child exited 1 after an authenticated BDD pass").

## Root cause
`evaluate_module_items` (`src/compiler_rust/compiler/src/interpreter_eval.rs`)
maps `main`'s returned value to the exit code. For `fn main() -> ()` the
interpreter returns the implicit tail expression, so a tail `describe(...)` /
`f()` returning `true` exited 1 (an `i64` tail exited with that value). Reached
whenever the JIT demotes to the interpreter (e.g. a spec with a module docstring).

## Fix
A `main` that explicitly declares `()` or `Nil` return exits 0 regardless of its
tail value (`main_declares_unit_return`), on both the engine-driven and default
paths. Int-typed `main` still propagates its value.

## Check
`sh scripts/check/check-unit-main-exit-code.shs [SIMPLE_BINARY]` runs real child
processes: unit/Nil-typed mains with bool/int tails must exit 0; `simple test`
on an all-pass spec must exit 0 and on a failing spec nonzero; controls: int
`main` returns 7, JIT path unaffected.

## Evidence
RED (tip seed before fix): see PR body. GREEN: rebuilt seed, see PR body.

## Not covered
Pure-Simple (non-seed) test runner exit mapping; only the seed interpreter.
