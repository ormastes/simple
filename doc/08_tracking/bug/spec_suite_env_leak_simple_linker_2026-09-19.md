# `native_linking_internal_spec` fails only in suite context (SIMPLE_LINKER)

- **Filed:** 2026-09-19 by lane E1 (COFF/PE). **Not an E1 defect** — E1 touches
  neither spec, and both were green before and after this lane's changes.
- **Owner:** whoever owns the test runner / spec isolation.
- **Status:** open, reproduced, root cause narrowed but not proven.

## Symptom

Running the linker spec directory as a suite gives **424/426**. The failing
example is `native_linking_internal_spec.spl`'s

> "SIMPLE_LINKER unset still resolves through the external path unchanged"

It **passes standalone and fails only in suite context**, which makes it an
isolation defect rather than a defect in the assertion.

## Reproduction

```
# passes
bin/simple test --no-session-daemon \
  test/01_unit/compiler/backend/linker/native_linking_internal_spec.spl
#   outcome=OK declared>=5 executed=5 passed=5 failed=0

# fails, as one example out of 426, when the directory is run as a suite
# (the Rust seed runner rejects a directory argument — "expected .spl test
#  file" — so this needs the pure-Simple runner or an explicit multi-file run)
```

Every linker spec, including this one, is green when run one file per process:
27 files, 0 not-green, measured on `b637262cbb1`.

## What was checked

`SIMPLE_LINKER` is written by exactly two specs,
`link_engine_external_spec.spl` and `native_linking_internal_spec.spl`, each
through its OWN private copy of this helper (duplicated, not shared):

```
fn with_env(key: text, value: text, block: fn()):
    val previous = rt_env_get(key) ?? ""
    rt_env_set(key, value)
    block()
    rt_env_set(key, previous)
```

Two candidate mechanisms, one ruled out and one open:

**Ruled out — restoring an unset variable to `""`.** `previous` is `""` when
the variable was absent, so the restore *sets* it empty instead of unsetting
it. Measured, that is not observable by this consumer: `rt_env_get` returns
nil for a set-to-empty variable under this binary (probe: `unset -> present=nil`,
`set-to-empty -> present=nil`), and `mold.spl:143` reads it as
`(env_get("SIMPLE_LINKER") ?? "").trim()`. Unset and set-empty are
indistinguishable here.

**Open — no restore when the block does not return normally.** `block()` is
not protected, so an assertion failure or early exit inside a
`with_env("SIMPLE_LINKER", "internal", ...)` example leaves the variable set
for every later spec in the same process. This is consistent with "fails only
in suite context".

**Also open, and possibly the real cause — ambiguous `env_get` dispatch.** Both
specs declare `extern fn rt_env_get(key: text) -> text` (non-optional) while
the runtime also has an optional-returning form, and the runner already warns
on every run of these files:

> warning: public function `env_get` has 4 co-compiled definitions with 2
> differing signatures ((text)->Optional(text) vs (text)->text); JIT call sites
> resolve by exact arg-type match ... falling back to the last definition when
> types are ambiguous — a fallback hit may still dispatch to the wrong one.
> [compiler_cross_module_private_symbol_collision]

A suite run co-compiles more modules than a standalone run, so which definition
an ambiguous call site binds to can differ between the two — exactly the
context-dependence observed. This warning is emitted, not hypothetical.

## What must NOT be done

Do not make the failing example tolerate a set-but-empty `SIMPLE_LINKER`, and
do not reorder the specs to hide it. The assertion is correct; the isolation is
not. A fix belongs in one of: a shared `with_env` that restores on any exit and
can truly unset, or the `env_get` signature collision.
