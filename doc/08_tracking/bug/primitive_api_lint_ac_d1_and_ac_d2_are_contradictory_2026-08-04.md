# primitive_api lint: AC-D1 and AC-D2 assert opposite verdicts on the same signature shape

**Status:** ARCHITECTURAL-OPEN — confirmed genuine spec/rule-design
contradiction, not a code bug (re-verified 2026-08-09, final terminal-status
pass 2026-08-10: `_all_same_primitive` at
`src/compiler/90.tools/fix/rules/impl_/lint_primitive_api.spl:160` unchanged,
contradiction still reproduces exactly as described; resolving it requires an
owner to choose an AST/body-aware discriminator, a deliberate `deny`-level
lint-semantics change, not a drive-by fix)
**Found:** 2026-08-04

## Re-verification (2026-08-09)

Re-read `check_primitive_api` in
`src/compiler/90.tools/fix/rules/impl_/lint_primitive_api.spl` (current lines
94-140): it is still the same single-line text scan described below —
`_all_same_primitive(all_types)` is computed over `params + return_type`
combined, with no distinction between "single primitive param mirroring
return" (AC-D1, must NOT flag) and "single primitive param mirroring an
extern's primitive signature" (AC-D2, must flag). `test/system/code_quality/
primitive_api_lint_spec.spl` still has both `AC-D1` (line 72) and `AC-D2`
(line 116) examples asserting opposite verdicts on textually-identical
declaration shapes (`fn(x: i64) -> i64`), differing only in the function
body, which the text-scan rule structurally cannot see.

This is confirmed as a genuine specification contradiction, not an
implementation defect: no line-oriented predicate over the declaration line
alone can satisfy both examples, because their declaration lines are
identical modulo the function name. Making the rule AST/body-aware (checking
whether the body is a pass-through call to an `extern fn` with a matching
signature, as AC-D2's own comment implies) would resolve it, but that is a
`primitive_api` lint **semantics change** at `deny` level
(`src/compiler/90.tools/lint/_LintMain/config_and_model.spl:148`), which would
immediately alter fail/pass status tree-wide — a lint-design decision for an
owner to make deliberately, not a safe drive-by fix. Left OPEN and
unmodified; no code or spec change made in this pass, per the standing
guidance not to force a code change when the real issue is a spec/rule
inconsistency.

## Symptom

`test/system/code_quality/primitive_api_lint_spec.spl` has one permanently red
example:

```
✗ AC-D2: should STILL flag a regular pub fn that mirrors an extern signature
    expected 0 to be greater than 0
```

Repro (both examples are in the same file):

```
# AC-D1 (line 71) — passes today, expects 0
pub fn negate(x: i64) -> i64:
    return 0 - x
expect(count_primitive_api_fixes(source)).to_equal(0)

# AC-D2 (line 116) — fails today, expects > 0
pub fn wrap_alloc(size: i64) -> i64:
    return rt_alloc(size)
expect(count_primitive_api_fixes(source)).to_be_greater_than(0)
```

The two signatures are the **same shape**: one parameter whose type equals the
return type, both the same bare primitive. Only the function body differs.

## Root cause

`check_primitive_api` in
`src/compiler/90.tools/fix/rules/impl_/lint_primitive_api.spl:96` is a
**line-oriented text scan** — it only ever looks at the single line a `pub fn`
is declared on. The pure-math exemption it applies is

```
# lint_primitive_api.spl:145
fn _all_same_primitive(types: [text]) -> bool:
    if types.len() < 2:
        return false
    ...
```

where `types` is params + return type. For `wrap_alloc(size: i64) -> i64` that
list is `["i64", "i64"]` — length 2, all equal, all bare primitive — so
`is_pure_math` is true and the function is skipped, yielding 0 fixes. It is the
**D-1 pure-math exemption**, not the D-2 extern exemption, that suppresses
AC-D2.

Narrowing `_all_same_primitive` to require ≥2 *parameters* (rather than ≥2
total types) would make AC-D2 fire — but it would then also fire on `negate`,
turning AC-D1's "should NOT flag single-arg single-return same-primitive fn"
red. The two criteria cannot both hold under any predicate over the declaration
line alone, because the declaration lines are identical modulo the function
name.

Confirmed the rule sees only the declaration line: the loop at
`lint_primitive_api.spl:100-105` tests `trimmed.starts_with("pub fn ")` and
extracts params/return from that same `line`; the body line
(`return rt_alloc(size)`) is never inspected by this rule.

## Why not fixed now

Satisfying both criteria requires a signal the current rule does not have —
the most likely intended one being "the body is a pass-through to an `extern
fn`" (AC-D2's own comment says *"Same shape as extern, but declared pub fn"*).
That is a semantic/AST rule, and `primitive_api.spl`'s `check_call_site` is
named in this file's own comments as the AST-driven counterpart, so the right
home is probably there rather than in the text-scanning EasyFix rule. Choosing
the discriminator is a lint-design decision: it changes what `primitive_api`
means, and `primitive_api` is at `deny` level
(`src/compiler/90.tools/lint/_LintMain/config_and_model.spl:148`), so a
widened rule would immediately fail builds across the tree. Neither example was
weakened; the contradiction is recorded so an owner can pick which reading
wins.

---

## Re-verification 2026-08-17 (compiler-lint lane) — ARCHITECTURAL-OPEN, still stands

Classified by CONTENT of current source, not SHA ancestry.

`src/compiler/90.tools/fix/rules/impl_/lint_primitive_api.spl` is **unchanged**
in the respect this record is about: `_all_same_primitive` still derives its
verdict from the declaration line alone, and the scan loop still keys on
`trimmed.starts_with("pub fn ")` with params/return extracted from that same
`line`. No body/AST signal was added.

Therefore the contradiction recorded on 2026-08-04 is intact: AC-D1 (do not
flag a single-arg single-return same-primitive `pub fn`) and AC-D2 (flag an
extern-shaped `pub fn`) remain unsatisfiable simultaneously by any predicate
over the declaration line, because the two declaration lines are identical
modulo the function name.

**Verdict: ARCHITECTURAL-OPEN, not a code defect to patch.** Resolving it is a
lint-design decision (which reading of `primitive_api` wins) and, because the
rule sits at `deny` level, a widened rule fails builds tree-wide. No patch
applied; no spec written, because there is no defect to make go red — a spec
here would only encode one arbitrary side of the contradiction.
