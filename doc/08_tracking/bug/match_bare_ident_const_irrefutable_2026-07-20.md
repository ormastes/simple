# `match` arm naming a `val` constant lowers as an irrefutable capture

**Status (2026-07-20):** OPEN. Worked around at every known call site; no root
fix yet. Distinct from `native_const_pattern_lowers_irrefutably_2026-07-13.md`
(that one is enum-variant-vs-struct *name precedence* in native lowering, and is
resolved) — this one is a **bare identifier that resolves to a `val` constant**
being treated as a fresh binding name instead of a value to compare against.

## Symptom

A `match` whose arms are bare identifiers naming module-level `val` constants
always takes the **first** arm, whatever the subject is:

```simple
val ITF_ERR_AUTH = "auth"
val ITF_ERR_USAGE = "usage"

fn exit_code(kind: text) -> i64:
    match kind:
        ITF_ERR_AUTH: 4      # <- always taken
        ITF_ERR_USAGE: 2
        _: 1
```

`exit_code(ITF_ERR_USAGE)` returns `4`. The first arm is compiled as a capture
binding (`ITF_ERR_AUTH` shadowing the subject), which matches everything, so no
later arm — including `_` — is ever reachable.

## Impact

Silent and total: every error kind in `src/app/devhub/errors.spl` exited `4`
("auth") regardless of the real failure, which also hid four long-standing
`itf_config_spec` failures dating to 2026-05-19. The failure mode is invisible in
review — the code reads exactly like a correct value match — and specs that
exercise only the first arm stay green.

## Reproduction

Run the snippet above through `bin/simple run`. Verified 2026-07-20 on the
deployed seed binary:

```
auth  -> 4  (expect 4)
usage -> 4 (expect 2)     <- wrong: first arm captured the subject
```

The production instance is fixed, so reproduce with a fresh file rather than
expecting `errors.spl` to still show it.

## Required fix

In match lowering, resolve a bare identifier pattern against the enclosing scope
**before** treating it as a binding: if it names a `val` constant, lower it as an
equality test on that constant's value; only fall back to a capture binding when
the name is genuinely unbound. A capture in a non-final arm that makes every
later arm unreachable should also be a lint/warning in its own right.

## Workaround (in use today)

Compare explicitly with `==` in an `if`/`elif` chain. See `exit_code()` in
`src/app/devhub/errors.spl`, which carries a comment pointing back here.

## Audit scope

~37 files in the repo use `match` on a bare identifier. Not all are defects —
only those whose arm identifiers resolve to `val` constants (arms that are
string/number literals or enum variants are unaffected). Each needs checking
against this rule before it can be declared clean.
