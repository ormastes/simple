# `match` arm naming a `val` constant lowers as an irrefutable capture

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

**Status (2026-07-20 -> CLOSED-STALE 2026-09-12):** OPEN. Worked around at every known call site; no root
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

## Re-measured 2026-09-07 on the pure-Simple interpreter — STILL OPEN, now pinned

The bug DB routes this row to
`src/compiler/10.frontend/core/interpreter/eval.spl`. That attribution is
correct for the engine but the defect is NOT fixable there today, and this note
records the measurement rather than leaving the row unexamined.

**LANE:** pure-Simple tree-walk evaluator, `match_pattern` in
`src/compiler/10.frontend/core/interpreter/eval.spl`, driven directly from a
spec over a hand-built AST (`use compiler.core.interpreter.eval.{eval_expr}`).
No deployed self-hosted binary is needed — the Rust seed is only the host.
Binary identity: `bin/release/aarch64-unknown-linux-gnu/simple`, 50093192
bytes, 2026-09-06 09:59.

Reproduced: `match 2:` with a single arm `case WS_OPCODE_TEXT:` binds `2` to
`WS_OPCODE_TEXT` and takes the arm. `match_pattern`'s `EXPR_IDENT` branch ends
in `env_define(name, value_id); return true` for any identifier that is not
`_`, not `None`, and not a declared enum variant.

**Why it is not fixed here.** The sibling row
`case_bare_ident_is_irrefutable_binding_2026-08-01.md` WAS fixed on this engine
on 2026-09-07, but only for its Probe-A half: a boxed-enum scrutinee gives the
evaluator a discriminator (`val_is_boxed_enum`) it can key on. The const shape
has no such discriminator:

- the scrutinee is an `i64`/`text`, which carries no type identity to consult;
- `env_lookup` cannot tell a module-level `val` constant from an ordinary outer
  local, so "compare when the name resolves" would turn a legitimate shadowing
  binder into a comparison — a feature deletion, not a fix;
- spelling alone (`SCREAMING_SNAKE`) is a heuristic, not resolution, and would
  reject valid code.

This is the same call the Rust seed made and documented in the sibling record:
"this seam cannot tell a const pattern from a binder without const resolution,
and a false positive would reject valid code."

**Unblock condition:** const resolution reaching `match_pattern` — the
evaluator must be able to ask whether a bare identifier names a module-level
constant declaration, not merely whether some binding of that name is
reachable. Until then the `==`/`elif` workaround in
`src/app/devhub/errors.spl` stays correct.

**Pinned, so a future change is deliberate:**
`test/01_unit/compiler_core/interpreter/bare_case_ident_variant_pattern_spec.spl`
carries the row "leaves a capitalized arm on a NON-enum scrutinee a binder",
which asserts today's (wrong) behaviour explicitly and names this record. A
const-resolution fix must flip that row on purpose.

## Triage 2026-09-12
Older than 45 days; a workaround is already documented at every known call site. Closing per age policy. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
