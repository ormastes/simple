# `generator` identifier collides with a builtin/reserved construct name

**Status:** OPEN — found 2026-08-11 during a stdlib bug hunt in
`src/lib/nogc_async_mut/generator.spl`.

## Symptom

`use std.generator.{generate_range, take}` followed by using either imported
symbol fails with `semantic: generator expects a lambda` — this breaks the
exact usage pattern documented in `generator.spl`'s own header comment.

## Root cause (not yet investigated to completion)

The module name `generator` appears to collide with a builtin/reserved
construct name in the parser or semantic analyzer (likely related to a
`generator { ... }` block/coroutine construct elsewhere in the language). The
import resolves to the wrong symbol, causing the semantic checker to treat
a call through it as invoking that construct instead of the stdlib function.

## Reproduction

Minimal repro built at (ephemeral scratch, not committed):
`/tmp/claude-1000/-home-ormastes-dev-pub-simple/895f85cb-815f-448b-86ed-4708de028caa/scratchpad/gen_test.spl`
— re-derive via: import `generate_range`/`take` from `std.generator` and call
either.

## Next steps

- Confirm whether `generator` is a reserved keyword/soft-keyword in the
  parser (`src/compiler/10.frontend/**`) and whether the module name needs to
  be renamed, or whether import resolution needs to prefer the explicit
  `use std.generator.{...}` binding over the reserved construct.
- Fix at the resolution/parser layer — do not work around it by renaming the
  stdlib module, since that would just hide a real name-resolution defect.
