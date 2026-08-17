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

## 2026-08-17: frontend half closed; the reported swallow is NOT in this lane

Measured, not inferred. The 2026-07-17 sub-case above guessed the defect lived
in `flat_bridge_build_string_interps` / `split_interpolation_segments`. It does
not. `parse_interpolation_fragment`
(`src/compiler/10.frontend/core/string_interpolation_expand.spl:35`) already
returned `-1` for the reported **whitespace-padded** shapes `" {inner} "` and
`" {inner}"` before any change today — proven by deleting the new guard and
re-running the spec, which still passed. With the fragment rejected the whole
string falls back to a verbatim literal, which is exactly what the oracle
prints. So the pure-Simple frontend never produced the empty-string swallow;
the remaining `N1:|END` report belongs to the other lowering lane and could not
be reproduced here (see "not proven" below).

What the sweep DID find, via the generalizing spec rather than the reported
repro: the class was handled **inconsistently**. The padded spellings were
rejected only because the padding fails to parse — `.trim()` is not normalising
these fragments — while the **unpadded** `{inner}` / `{a: 1}` / `{1, 2}` parsed
cleanly as dict/set literals and were accepted as interpolations, the precise
shape that lowers to nothing. Only half the class was safe, by accident.

Fix: `interpolation_fragment_is_brace_literal` (same file) rejects any region
whose first non-blank character opens a brace literal, so the verbatim fallback
is uniform. Leading blanks are skipped explicitly rather than by `.trim()`,
because the padded-vs-unpadded split is itself evidence the trim does not
normalise here. Regression spec:
`test/01_unit/compiler/frontend/interp_brace_literal_fragment_spec.spl`
(before: `Results: 3 total, 2 passed, 1 failed`; after: `Results: 3 total, 3
passed, 0 failed`).

**Not proven:** the native/`native-build` lane. `bin/simple` is a Rust
bootstrap seed and no self-hosted binary is deployed, so the `N1:|END` output
in the 2026-07-17 note could not be re-measured; this change fences the
pure-Simple frontend only. Also unproven: whether an unpadded `{...}` region is
reachable from source at all (`"{{inner}}"` is consumed by the `{{` escape
first) — the guard closes it as a latent trap regardless.

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

## 2026-08-17 (later): the fix was CLOBBERED and restored; today's spec run is UNVERIFIED

`e14a2ffb4df` ("three fail-open sites made fail-closed") was a stale-snapshot
clobber, not a deliberate revert. It silently deleted
`interpolation_fragment_is_brace_literal` and its guard call from
`src/compiler/10.frontend/core/string_interpolation_expand.spl` (−32/+0) and the
"frontend half closed" section of THIS record (−32/+0), while leaving
`test/01_unit/compiler/frontend/interp_brace_literal_fragment_spec.spl` in place
at origin. `git grep interpolation_fragment_is_brace_literal origin/main -- src/
test/` returned zero hits, so nothing superseded the fix — it was simply gone,
and the spec was fencing an implementation that no longer contained the fix.

Restored here per-hunk from `e14a2ffb4df^` (never by `git revert`, which would
have rewound the clobber's legitimate fail-closed payload and the int61
restoration `1983ecdbce9f`).

**The ablation could NOT be reproduced today, and this is recorded as
UNVERIFIED rather than as a pass.** Measured with the Rust seed
`bin/release/x86_64-unknown-linux-gnu/simple` (size 59537240, mtime 2026-08-17
12:58:51 UTC), three runs — two on an isolated `git worktree` pinned at
`origin/main` (reverted arm) and one on the restored tree (applied arm). All
three produced the identical verdict:

```
SPEC FILE VERDICT: test/01_unit/compiler/frontend/interp_brace_literal_fragment_spec.spl declared>=1 executed=0 passed=0 failed=1 dropped=1 unrun=1 reason=child-died-by-signal
Results: 0 total, 0 passed, 0 failed
```

with the runner's own diagnosis:

```
error: test-runner: TERMINATED: child died by signal with no crash sentinel and no fault diagnostic (unverified -- an external killer such as earlyoom cannot be ruled out)
```

So the answer to "is the spec RED or vacuously green at origin" is **neither**:
`executed=0` — it never ran a single `it`, in either arm. It is not an oracle on
this host today. Because both arms are byte-identically unverified, the run also
does not indicate the restoration made anything worse; the restoration is
verified by CONTENT (identical to the parent's design) plus the contemporaneous
`2 passed, 1 failed` -> `3 passed, 0 failed` measurement recorded in the section
above, not by a re-run. A host with memory headroom should re-run this spec and
replace this paragraph with a real two-arm result.
