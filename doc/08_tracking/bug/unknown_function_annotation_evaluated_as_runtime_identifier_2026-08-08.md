# Unknown function annotation `@X` is evaluated as a runtime identifier instead of erroring at parse time

- **ID:** unknown_function_annotation_evaluated_as_runtime_identifier_2026-08-08
- **Status:** OPEN (deliberately not fixed in the change that found it)
- **Severity:** medium (fail-open; converts a compile-time typo into a
  module-load failure in an unrelated place, and lets never-implemented
  annotations ship silently)
- **Date:** 2026-08-08

## What happens

The Rust seed interpreter
(`src/compiler_rust/compiler/src/interpreter_eval.rs`, function-decorator
application) applies every `@X` on a function as a Python-style runtime
decorator: it evaluates the bare identifier `X` in the module env, unless `X` is
on a small hardcoded skip-list. An annotation that is not a real runtime value
and not on the skip-list therefore produces, at MODULE LOAD time:

```
error: semantic: variable `X` not found
```

Demonstrated with `@zzbogus` on a 3-line module: 0 examples executed.

## Why this matters

This fail-open is how `@noalloc` — documented, referenced by
`src/compiler/35.semantics/noalloc_checker.spl`, and carried by shipped stdlib
modules under `src/lib/nogc_async_mut_noalloc/` — sat in the tree with **zero
parser registration in either implementation** until 2026-08-08. Nothing ever
rejected it; it simply became a latent load failure on the interpreter path,
invisible to `bin/simple run`. See
`noalloc_decorator_unbound_in_seed_interpreter_2026-08-08.md`.

## Desired behaviour

An `@X` that is neither a known compiler annotation nor a resolvable decorator
value should be a **parse/semantic error at the annotation site**, naming the
annotation and the file — not a deferred "variable not found" from the module
env.

## Why it was not fixed here

Making unknown annotations fail closed would reject every other unwired
annotation in the tree simultaneously, which is a separate survey-and-migrate
job. The blast radius must be enumerated first: sweep all `@` annotations used
across `src/` and `test/`, diff against `KNOWN_DECORATORS` / `KNOWN_ATTRIBUTES`
in `src/compiler_rust/compiler/src/lint/checker_core.rs` and the dispatch chain
in `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl`, and
register or delete each straggler before flipping the gate.

Note the pure-Simple parser does not have this specific defect — it drops
unknown module-level decorators silently rather than synthesising an identifier
expression. That is a *different* fail-open (silent drop) and should be closed
by the same survey.
