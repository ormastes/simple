# Literal `{ ... }` sharing a string with other `{placeholder}`s is silently swallowed, not interpolated

**Date:** 2026-07-03
**Severity:** P2 (silent wrong output, not a crash)
**Status:** open
**Related:** `interp_brace_literal_scope_corruption_2026-06-12.md` (no-identifier
brace corrupts HIR lowering scope), `string_interp_brace_across_concat_literals_2026-07-03.md`
(brace spanning concatenated literals leaks source text), `parser_grid_identifier_keyword_collision_2026-07-03.md`
(unrelated `grid` keyword collision, found in the same session)

## 2026-07-17 follow-up: minimal nested-brace case is swallowed to EMPTY, not verbatim (lane S47, task #178 round 2)

Regression-checking this doc's own "s2 JSON/SDN-shaped repro is unchanged and
does NOT regress" claim (which was re-verified correct for
`"{ x {inner} y }"`-shaped strings — outer opening has literal text before the
nested placeholder) turned up a **narrower** sub-case this doc's fix does not
cover: when the outer brace span has **no other literal text**, only
whitespace, around the nested placeholder — `"{ {inner} }"` or
`"{ {inner}}"` — the native path does not fall back to verbatim literal text
(as the oracle does, and as the documented `s2`-class behavior promises).
Instead it **silently swallows the entire span to an empty string**, which is
a *different and worse* failure mode than the one this doc's "Expected"
section describes.

```simple
fn main():
    val inner = 9
    print "N1:{ {inner} }|END"
    print "N2:a{ {inner} }b|END"
    print "N3:{ {inner}}|END"
```

- Oracle (`bin/simple run`): `N1:{ {inner} }|ENDN2:a{ {inner} }b|ENDN3:{ {inner}}|END`
  (verbatim fallback in all three, consistent with the documented `s2` class).
- Native (`native-build`, `SIMPLE_BOOTSTRAP` unset): `N1:|ENDN2:ab|ENDN3:|END`
  — the entire `{ ... }` span (including surrounding whitespace) vanishes with
  no error, leaving only whatever literal text was outside it.

For contrast, the already-fixed `{{`/`}}` escape and the wider `{ x {inner} y
}` shape (extra literal text alongside the nested placeholder, not just
whitespace) both still match the oracle exactly on the current tip
(`ffc0c360ba4`, fetched 2026-07-17) — this is specifically the
whitespace-only-padding-around-a-lone-nested-placeholder shape that regresses
to a silent empty string instead of a literal-text fallback.

**Status:** open sub-case, not yet root-caused to an exact line. Likely in the
same `flat_bridge_build_string_interps` (frontend bridge) /
`split_interpolation_segments` (`50.mir/_MirLoweringExpr/expr_dispatch.spl`)
region this doc's main fix touched — the positional-alignment contract
between "regions" and "interps" probably drops the region's captured literal
text entirely in this shape instead of falling back to it. Left for a
follow-up session rather than fixed inline (shared frontend/MIR positional
contract, not a small isolated change, per this lane's fix-vs-file
threshold).

## Symptom

A double-quoted interpolated string that contains a literal `{ ... }` span
(e.g. emitting SDN/JSON-like dict syntax) *and* one or more real
`{placeholder}` interpolations elsewhere in the same literal does not error —
it silently prints the entire `{`-to-matching-`}` span verbatim, placeholders
inside included, instead of interpolating anything in that span. A clean
placeholder with no surrounding literal braces in the same string (e.g.
`"...{seed}..."`) interpolates fine right next to the broken span.

## Repro

```simple
fn main() -> i64:
    val x: i64 = 5
    val s1 = "before {x} literal { brace } after"
    print s1        # ERROR: semantic: variable `brace` not found
                     #  (a literal `{ ident }` with no other placeholders in
                     #   the literal is instead treated as a bad placeholder
                     #   and hard-fails)

    val s2 = "{ eye: [0.0, {eye_z}] }"
    print s2         # prints "{ eye: [0.0, {eye_z}] }" verbatim — no crash,
                     # no interpolation of {eye_z}, just silently wrong
    0
```

Two different failure modes depending on shape: a bare `{ word }` with no
other real placeholder in the string hard-errors ("variable not found"); a
`{ ... {real_placeholder} ... }` span (SDN/JSON-shaped, matching braces
containing a nested real placeholder) instead swallows the whole span as one
failed-to-parse expression and falls back to printing it as literal text —
including the still-unresolved inner `{eye_z}`.

## Workaround (confirmed)

Double the literal braces — `{{`/`}}` — exactly like Python f-strings / Rust
`format!`:

```simple
val s2 = "{{ eye: [0.0, {eye_z}] }}"   # -> "{ eye: [0.0, 11.2] }" — correct
```

Applied in `src/app/model3d/main.spl` (`_gen_heightmap_text`), which emits
`camera: { ... }` and per-node `{ ... }` SDN dicts inside interpolated
strings.

## Expected

A literal `{`/`}` pair with no valid identifier/expression immediately after
`{` (or containing nested `{other}` placeholders that read as sub-expressions
rather than a lookup on the immediate identifier) should require the same
`{{`/`}}` escape uniformly, with a clear parse-time diagnostic when it's
missing — not a silent swallow of the whole span in one case and a
context-free "variable not found" in the other.
