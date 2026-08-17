# `match` arm naming a `val` constant lowers as an irrefutable capture

**Status (2026-08-17):** SOURCE FIXED / LIVE EVIDENCE PENDING by the
`p2_match_const` SPipe lane. The pure-Simple MIR repair and exact/adjacent
regressions are present; execution awaits a provenance-admitted pure-Simple
CLI. The canonical BugDB row remains owned by the sweep merge owner. Distinct from
`native_const_pattern_lowers_irrefutably_2026-07-13.md`
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

### Compiler trace and blocked verification (2026-07-27)

The flat frontend currently converts every bare identifier pattern to
`PatternKind.Binding` in `_FlatAstBridge.convert_flat_pattern`. HIR then creates
a fresh variable for that binding. MIR treats it as the irrefutable/default arm.
MIR also builds `norm_arms`, but the scalar dispatch loop iterates the original
`arms`, so even successful normalization is discarded outside the enum path.

The scoped repair is:

1. resolve immutable current-module scalar constants before enum/capture
   classification;
2. dispatch the normalized arms rather than the original arms;
3. add a strict native regression where the second constant arm returns `29`
   and the wildcard remains reachable.

Integer constant normalization was prototyped but not accepted: the available
source-driver build failed on missing `rt_transient_array_scope_begin` after
JIT fallback, so no green compiler artifact exists. Text and boolean constants
also require their own non-integer literal lowering rather than being inferred
from the integer candidate.

## Workaround (in use today)

Compare explicitly with `==` in an `if`/`elif` chain. See `exit_code()` in
`src/app/devhub/errors.spl`, which carries a comment pointing back here.

## Audit scope

~37 files in the repo use `match` on a bare identifier. Not all are defects —
only those whose arm identifiers resolve to `val` constants (arms that are
string/number literals or enum variants are unaffected). Each needs checking
against this rule before it can be declared clean.

## Pure-Simple repair (2026-08-17)

The MIR owner now resolves a Binding-shaped arm against the current module's
folded scalar constants before enum or capture classification, converts exact
int/bool/text values to literal patterns, and dispatches the resulting
`norm_arms`. Scalar literal chains compare text through `rt_text_eq_any` and
retain the existing integer jump-table path when every case is an integer.

Regression coverage is in
`test/01_unit/compiler/codegen/match_bare_val_constant_spec.spl`: the exact
two-text-constant failure, the previously requested second integer arm
returning 29, adjacent boolean constants, wildcard reachability, and a genuine
unbound capture (including a same-named mutable module `var`). Live execution
remains pending because this worktree has no
provenance-admitted pure-Simple CLI; the Rust seed was deliberately not used.

## Knowledge update scope

- Match feature and MIR layer expert notes now record constant-before-capture
  resolution and normalized-arm dispatch.
- `doc/07_guide/`: N/A; this repairs existing language semantics and exposes no
  new user command or capability.
- Research/architecture/design: N/A; ownership remains in canonical MIR match
  lowering.
- Workflow/SPipe/manual docs: N/A; no workflow or scenario-manual contract
  changed.
