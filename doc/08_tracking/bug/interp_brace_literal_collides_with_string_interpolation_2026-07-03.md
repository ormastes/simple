# Literal `{ ... }` sharing a string with other `{placeholder}`s is silently swallowed, not interpolated

**Date:** 2026-07-03
**Severity:** P2 (silent wrong output, not a crash)
**Status:** open
**Related:** `interp_brace_literal_scope_corruption_2026-06-12.md` (no-identifier
brace corrupts HIR lowering scope), `string_interp_brace_across_concat_literals_2026-07-03.md`
(brace spanning concatenated literals leaks source text), `parser_grid_identifier_keyword_collision_2026-07-03.md`
(unrelated `grid` keyword collision, found in the same session)

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
