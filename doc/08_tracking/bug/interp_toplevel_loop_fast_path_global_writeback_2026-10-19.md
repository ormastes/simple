# Seed interpreter: top-level loop fast paths lose module-global writes

- **Status:** fixed (seed interpreter, `work/interp-toplevel-while-fastpath`)
- **Found:** 2026-10-19, base `origin/release_phase3` @ `630f773bdc7`
- **Component:** `src/compiler_rust/compiler/src/interpreter_control.rs` (while/for
  shape fast paths), `src/compiler_rust/compiler/src/interpreter/node_exec.rs`
  (compound assignment)

## Symptom

```
fn inc(x: i64) -> i64:
    x + 1
var a = 0
var i = 0
while i < 5:
    a = inc(a)
    i = i + 1
print(a)        # printed 0, expected 5
```

Correct inside a function and under `SIMPLE_COVERAGE=1` (which skips the fast
paths).

## Root cause

A top-level `var` lives in `env` as a NON-local binding and in `MODULE_GLOBALS`
(`interpreter_eval.rs` main loop, `record_flattened_global`). The identifier
read treats `MODULE_GLOBALS` as authoritative for non-local names
(`interpreter/expr/literals.rs`, the `!env.is_local(name)` branch). The generic
`=` path syncs `MODULE_GLOBALS` after `env.insert` (`node_exec.rs`, "Also sync
to MODULE_GLOBALS"). Every shape fast path instead read `env.get(..)` and wrote
`env.insert(..)` only, so:

- the loop result never reached `MODULE_GLOBALS` and the next read returned the
  pre-loop value (write side);
- a loop entered after a function had updated the global through
  `MODULE_GLOBALS` started from the stale `env` copy (read side).

The compound-assignment identifier path (`x += e`) had the same env-only write,
independent of any fast path: top-level `i += 1` was a no-op, so
`while i < 5: i += 1` never terminated (both with and without coverage).

## Affected forms (base, interpreter)

| form at top level | base | coverage (generic walk) |
|---|---|---|
| `while`: `a = inc(a)` (one-arg helper) | 0 | 5 |
| `while`: `a = add(a, i)` (two-arg helper) | 0 | 10 |
| `while`: `a = a + i` (direct int) — `i` also lost | 0 / 0 | 10 / 5 |
| `while`: `a = a + f(i, 2)` (inline int expr) | 0 | 20 |
| `for k in 0..5: a = a + k` | 0 | 10 |
| `while` inside top-level `if` | 0 | 5 |
| nested top-level `while` | 0 | 15 |
| loop after a function bumped the global | 10 | 15 |
| `i += 1` / `while i < 5: i += 1` | 0 / hang | 0 / hang |
| same loop inside a function | 5 | 5 |

## Fix

`fast_path_get` / `fast_path_store` in `interpreter_control.rs`. For a local
name both short-circuit on `env.is_local` and behave exactly as before. For a
non-local name the read declines the fast path unless the `env` copy is what the
identifier read would return, and the store mirrors the generic `=` path
(`env` + `MODULE_GLOBALS` when present). The int-range `for` fast path now
declines (instead of propagating an error) when an operand cannot be lowered.
The compound-assignment identifier path syncs `MODULE_GLOBALS` for non-local
names. Regression: `src/compiler_rust/compiler/tests/interpreter_toplevel_loop_fast_path_globals.rs`.

## Not fixed here (pre-existing, separate, both modes)

- A function reading a top-level `var` after a plain top-level assignment sees
  the initial value (`var a = 0; a = 5; get_a()` -> 0). The top-level write
  syncs only the flat `MODULE_GLOBALS`; the function frame resolves the name
  through the owner store.
- The same drift in an imported module's init: the init `while` does run
  (`print(j)` after it prints 3), but the following `w = j` is invisible to the
  module's own functions (`get_w()` -> 0), with and without coverage.
