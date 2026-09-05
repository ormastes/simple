# Unknown function annotation `@X` is evaluated as a runtime identifier instead of erroring at parse time

- **ID:** unknown_function_annotation_evaluated_as_runtime_identifier_2026-08-08
- **Status:** FIXED — see "Resolution (2026-08-08)" below
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


## Resolution (2026-08-08)

Fixed the general case rather than the `@noalloc` instance alone.

`src/compiler_rust/compiler/src/interpreter_eval.rs` (function-decorator
application): when the identifier lookup for a decorator that is not on the
compiler-directive skip list fails, the generic `variable \`X\` not found`
error (from deep inside expression evaluation) is now replaced with a
decorator-specific diagnostic naming both the annotation and the function:
`unknown decorator \`@X\` on function \`f\`` plus a help note explaining that
`X` is neither a recognised compiler annotation nor a function in scope to
use as a runtime decorator. Genuine user-defined runtime decorators (e.g.
`@double_result` in `test/03_system/feature/usage/decorators_spec.spl`) are
unaffected — the new path only fires when identifier resolution itself
fails, so it does not reject the language's real Python-style decorator
feature. A parse/check-time reject was considered and rejected: it cannot
distinguish a typo from a legitimate not-yet-defined runtime decorator
without evaluating the identifier, so resolution failure remains the only
sound discriminator.

The skip list (compiler directives that are never runtime-evaluated) was
also swept for other in-tree stragglers with the same defect shape and
expanded to include `alloc`, `no_alloc`, `no_mangle`, `gpu` (confirmed via a
RED probe: `@gpu` produced `variable \`gpu\` not found` before this fix, 1/1
pass after). `src/compiler_rust/compiler/src/lint/checker_core.rs`'s
`KNOWN_DECORATORS` whitelist was extended to match (plus `gpu_kernel`,
`gpu_device`, `gpu_shared`, which were already interpreter-skip-listed but
absent from the lint whitelist).

`@noalloc` is wired as a recognised non-runtime compiler directive (skip
listed in the interpreter, whitelisted in lint), consumed by
`src/compiler/35.semantics/noalloc_checker.spl` — not documentation-only.

Verified on a locally rebuilt seed
(`src/compiler_rust/target/release/simple`, NOT redeployed to
`bin/release/**`): `@zzbogus` (fabricated) now fails with
`unknown decorator \`@zzbogus\` on function \`zz_twice\`` instead of the old
`variable \`zzbogus\` not found`; `@inline @pure @unsafe @hardware` and
`@alloc @no_alloc @gpu @no_mangle` still pass 1/1 (no regression). A shadow
probe (`fn inline(f): return 999` defined alongside `@inline fn target(...)`)
showed `target` was NOT rebound to `999` — `@inline` does not reach this
runtime-decorator-application code path at all, so the "silently binds to an
unrelated in-scope symbol" half of this bug does not apply to the four
control annotations.

Also checked: `#[zzbogusattr]` (unknown attribute) stayed silent through
`bin/simple test` the same way `@zzbogus` did before this fix — confirming
`check_unknown_annotations`/`LintName::UnknownDecorator` (which does exist,
default level `Warn`) is not reached from the interpreter/test-execution
path at all; it is lint-only, and even a direct `lint <file>` invocation on
a probe file with `@zzbogus` did not surface it (reported "Lint passed: all
files clean"), so the `checker_core.rs` whitelist edit is list hygiene, not
an active gate today. Left as a separate, unfixed observation — out of
scope for this fix.

**Implementations touched:** Rust seed only
(`src/compiler_rust/compiler/src/interpreter_eval.rs`,
`src/compiler_rust/compiler/src/lint/checker_core.rs`). No `src/compiler/**`
(pure-Simple) change: grepping `src/compiler/**` found no function-decorator
*application* logic at all (only the module-level kind-171 decorator arm in
`_ParserDecls/enum_module_body.spl`, which silently drops unknown
module-level decorators — a different, still-open fail-open, not touched
here). The currently deployed `bin/release/x86_64-unknown-linux-gnu/simple`
itself still prints the Rust-seed WARNING banner (known Stage-3 self-host
blocker, see `.claude/rules/bootstrap.md`), so there is effectively one
active implementation right now and no separate pure-Simple runtime-decorator
behavior to reconcile yet.

This fix does **not** change the `hash`/`string` facade `export use`
calculus described in
`noalloc_decorator_unbound_in_seed_interpreter_2026-08-08.md` — that
remains gated on a redeploy, which remains blocked by the Stage-3
`unresolved type: ByteOrder` defect.
