# Literal `{ ... }` sharing a string with other `{placeholder}`s is silently swallowed, not interpolated

**Date:** 2026-07-03
**Severity:** P2 (silent wrong output, not a crash)
**Status:** partially resolved 2026-07-17 — two root causes found and fixed
in the native (pure-Simple) path; the original JSON/SDN-shaped repro (`s2`)
is unchanged and now understood to be an intentional architectural fallback
(see "2026-07-17 findings" below), matching the seed oracle's own behavior.

## 2026-07-17 findings and fixes

Reproduced both repro constructs at tip (9feac6ef6e5) via both the seed
oracle (`bin/simple run`, ground truth for grammar) and the native
(pure-Simple) `native-build` path. Found and fixed **two distinct, separate**
root causes in the native path, both in
`src/compiler/10.frontend/_FlatAstBridge/convert_nodes.spl`:

1. **Whitespace not trimmed before sub-parsing a placeholder.**
   `flat_bridge_parse_interp_inner` sub-lexed the raw `{ ... }` inner text
   *including* its padding spaces. `{x}` (no spaces) interpolated fine, but
   `{ x }` (spaces, the natural style for JSON/SDN-shaped text) silently
   failed to parse and fell back to printing the literal text verbatim, even
   for a perfectly valid declared variable — this was the actual root cause
   of the `s1` repro's inconsistency (`{x}` and `{ brace }` differ only in
   whitespace, not in "brace" being undefined). **Fix:** trim the inner text
   before lexing. `{ x }` now interpolates identically to `{x}`, and `{ brace
   }` (a real placeholder syntactically, referencing an undeclared variable)
   now correctly fails LOUD at HIR time with an "unresolved name" error —
   matching the seed oracle's own "variable not found" error class, instead
   of silently swallowing to literal text. This directly satisfies the
   "Expected" section's ask below: no more silent swallow for this case.

2. **`{{`/`}}` escaping (the documented workaround) was completely broken in
   the native path**, even though it works correctly in the seed oracle.
   `"...{{ instance }}..."` (used for real, e.g.
   `src/compiler/70.backend/backend/wasm_backend.spl` JS/WASM codegen text)
   previously either printed the doubled braces verbatim or hard-failed with
   "unresolved name" depending on padding, instead of collapsing to a single
   literal brace. **Fix:** taught `flat_bridge_build_string_interps` (parser
   bridge) and `split_interpolation_segments` (`50.mir/_MirLoweringExpr/expr_dispatch.spl`,
   MIR layer) to both recognize `{{`/`}}` as a literal-brace escape at the
   top level (matching each other exactly, so region positions stay aligned
   between the two layers), plus a small standalone `flat_bridge_decode_brace_escapes`
   helper for the case where a string is made of escapes only (no real
   placeholder) and so never reaches the MIR interpolation path at all.
   Verified this now matches the seed oracle byte-for-byte, including the
   doc's own confirmed workaround example.

   **Design note (why not "Some([]) as a signal"):** the natural design —
   pass `Some([])` (present but empty) through the HIR `interps` field to
   force the interpolation-lowering path even with zero real placeholders —
   does NOT work in this runtime. `[T]?`'s `Some([])` and `nil` are
   indistinguishable once they cross a HIR lowering boundary (an empty list
   and an absent value both come back `nil`/false on a `.?` check), so this
   signal silently degrades. Worked around it by decoding escape-only
   strings to their final literal text directly, before the interps field
   is even involved.

3. **The original `s2` JSON/SDN-shaped repro is unchanged and does NOT
   regress**: `"{ eye: [0.0, {eye_z}] }"` still prints verbatim
   (`{ eye: [0.0, {eye_z}] }`), matching the seed oracle exactly (the seed
   does the same thing — this was re-verified, not assumed). Root cause: the
   *lexer* merges nested braces into ONE region by brace-depth balancing
   before any placeholder-vs-literal decision is made, so
   `flat_bridge_build_string_interps` sees ONE big span
   (`" eye: [0.0, {eye_z}] "`) that is not a single clean expression, and (by
   original, intentional design — "preserves brace-bearing non-interp
   strings like CSS/JSON") falls back to literal for the *whole* string. A
   real fix for this specific shape requires MIR's
   `split_interpolation_segments` to independently re-validate each region
   (not just trust positional count against the interps list), which is a
   bigger, riskier redesign of the interps/segments positional-alignment
   contract between the frontend and MIR layers — out of scope for this
   fix. **This is the one part of the "Expected" section below not
   addressed.**

## Verification

- `sh scripts/check/native-smoke-matrix.shs`: `total=15 pass=15 fail=0
  codegen_fallback_hits=0` (including `string_interp`), both before and
  after the fix.
- Oracle-vs-native parity re-verified on 13 probes covering: the original
  `s1`/`s2` repros, `{{`/`}}` escaping (including the wasm_backend.spl-style
  pattern with no real placeholder), standalone unmatched `{`/`}`, `}}`
  alone with no preceding `{`, multi-line strings with real interpolation,
  and a plain unspaced `{ident}` sanity baseline. All match the seed oracle
  byte-for-byte except the known/documented `s2`-class JSON fallback, which
  matches the oracle's own (also-literal) behavior.
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
