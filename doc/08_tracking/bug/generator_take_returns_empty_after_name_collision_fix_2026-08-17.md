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
