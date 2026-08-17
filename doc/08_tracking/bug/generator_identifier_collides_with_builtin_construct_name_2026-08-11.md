# `generator` identifier collides with a builtin/reserved construct name

**Status:** FIXED 2026-08-17 (fix in source; needs a rebuilt seed to observe).

The speculated cause above (module-name collision / import resolution picking
the wrong symbol) was wrong. The real mechanism is builtin dispatch order in
the interpreter, and it does not involve imports at all: a *same-file*
`fn generator(initial, step_fn)` reproduces it identically. `eval_call`
(`src/compiler_rust/compiler/src/interpreter_call/mod.rs:480`) tries builtins
at Priority 2, before the user-function lookup at Priority 4, and
`builtins.rs`'s `"generator"` arm unconditionally required
`args[0]` to be a `Value::Lambda`. `std.generator`'s constructor takes
`(initial, step_fn)` — `args[0]` is the seed *value*, not the lambda — so
every call through `generate_range` / `generate_repeat` died with
`semantic: generator expects a lambda`.

Fix: `builtins.rs:538-546` returns `Ok(None)` (falling through to normal
function dispatch) when `functions` contains a user definition of `generator`,
so a user/stdlib definition shadows the lambda-based builtin. Same pattern as
the prelude-shadowing fences documented at `mod.rs:436-457`.

Regression coverage: `test/01_unit/compiler/parser_contextual_keyword_named_arg_spec.spl`
(mirrored to `test/unit/compiler/...`) — a user `fn generator` called
directly, called from a sibling function in the same module, and `generator`
used as a local binding name.

**Requires a rebuilt seed** — the deployed binary of 2026-08-16 predates the
fix and still reproduces.

Original (superseded) triage follows.

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
