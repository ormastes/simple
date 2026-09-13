# `std.generator` take() returns an empty array (2026-08-17)

Status: OPEN (P1)
Status re-verified 2026-08-17 by source inspection (triage shard 01).
**Status:** OPEN. Found while verifying the fix for
`generator_identifier_collides_with_builtin_construct_name_2026-08-11.md`.

## Relationship to the collision bug

The collision bug is genuinely fixed: `use std.generator.{generate_range, take}`
no longer dies with `semantic: generator expects a lambda`. But the header
comment's documented usage still does not produce the documented result — it now
fails *silently* instead of loudly, which is worse to detect and must not be
mistaken for the collision fix being incomplete or for the module working.

## Repro (verified 2026-08-17, seed built from `5f8ddf3b7aa` + `e85fd4aa8a1`)

```simple
use std.generator.{generate_range, take}

fn main():
    val g = generate_range(0, 3)
    print(take(g, 2))      # prints []  — expected [0, 1]
```

Exit code 0. `take(g, 2).len()` prints `0`.

## Where to look

`src/lib/nogc_async_mut/generator.spl`:

- `fn generator(initial, step_fn)` — the state-machine constructor.
- `fn take(generator, n)` = `iter_collect(iter_take(generator, n))`.

Either `generator(initial, step_fn)` is not producing an iterable the
`iter_take`/`iter_collect` pair recognises, or `iter_take` yields nothing for
this value shape. Both halves need probing separately before assigning blame —
the value produced by `generator(...)` should be printed directly first.

## Not verified

Behaviour under the pure-Simple self-hosted compiler. The pure-Simple compiler
has no `generator` builtin at all (`grep '"generator" =>' src/compiler` is
empty), so its dispatch path differs and must be measured on its own.

## Triage 2026-09-13

Ran the exact repro on `bin/simple` = Rust seed
`bin/release/aarch64-unknown-linux-gnu/simple` (symlinked from the shared main
worktree), sha256 `3d120a6f9ab5`, `Simple Language v1.0.0-rc.1`.

- `SIMPLE_EXECUTION_MODE=interpreter bin/simple run <repro>` -> prints
  `[0, 1]`. **Correct — this path is fixed.**
- `bin/simple run <repro>` (default execution mode, JIT/native) -> **SIGSEGV,
  exit 139** ("Segmentation fault", `timeout: the monitored command dumped
  core"). This is a *different and worse* symptom than the original report
  (silent `[]`, exit 0) — the same underlying default-mode generator/iterator
  dispatch defect now crashes instead of returning a wrong empty answer.

Status stays OPEN: the default (non-interpreter) execution path — the one a
plain `bin/simple run` takes — is still broken, and worse than filed. This is
a JIT/native codegen dispatch defect (closure-backed iterator state machine
under `iter_from_function`/`iter_take` mis-lowered), which lives in the
Rust-seed backend, not in `src/lib/nogc_async_mut/generator.spl` itself (that
file is correct, as proven by the interpreter-mode pass) — out of scope for a
pure-Simple lane fix. Left OPEN for a seed-side lane; the interpreter-mode
fix is recorded here so it is not re-investigated.
