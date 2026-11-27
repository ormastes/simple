# Literal `{ ... }` sharing a string with other `{placeholder}`s is silently swallowed, not interpolated

## 2026-11-25 — VERIFIED FIXED on release/1.0.0 (repro shapes all deterministic + diagnosed)

Verified on a `release/1.0.0` worktree @ `47d6c5eddd5` (Windows 11 / Git Bash),
runner: attr-capable Rust seed `simple.exe` executing the pure-Simple toolchain
sources (`SIMPLE_LIB=src`), plus `cargo test -p simple-parser --lib brace`
(31/31, incl. `brace_escape_strict` 7/7). The P2 defect this entry reports —
a literal `{ ... }` sharing a string with other `{placeholder}` holes being
**silently** swallowed or mis-parsed — no longer reproduces. Every repro shape
now has a deterministic value and a named diagnostic (`W-STR-BRACE-001` for
non-expression brace groups, an ordinary named semantic error for a valid hole
that references an undefined variable):

| Shape (doc repro) | release/1.0.0 behaviour |
|---|---|
| `"{ eye: [0.0, {eye_z}] }"` (s2) | `W-STR-BRACE-001` + kept as literal text (was: silent swallow) |
| `"N1:{ {inner} }"`, `"N2:a{ {inner} }b"`, `"N3:{ {inner}}"` (2026-07-17 sub-case) | `W-STR-BRACE-001` + verbatim fallback — never the empty string (was: swallowed to EMPTY on the native path) |
| `"before {x} literal { brace } after"` (s1) | `{ brace }` is a valid identifier hole: interpolates; undefined `brace` → named `semantic: variable 'brace' not found` (no silent wrong output) |
| `"a { b } {name} c"`, `"css {margin:0} then {name}"` | deterministic named diagnostic on every lane (no silent swallow) |
| `"{{ ... {x} ... }}"` escape | literal braces + working interpolation, no warning (the documented canonical form) |

New executable evidence:
`test/01_unit/compiler/frontend/interp_brace_literal_collision_spec.spl`
(11/11) pins the doc's exact repro shapes (s1, s2, N1/N2/N3) plus prevention
shapes: adjacent literal+placeholder, `{{`/`}}` escapes, braces inside nested
quotes, multiline strings, shell-snippet `sid(){ ...; }` groups, `{` at end of
string, and empty `{}`. Sibling evidence:
`string_interp_brace_escape_spec.spl` (6/6),
`interp_brace_literal_fragment_spec.spl` (3/3),
`flat_bridge_string_scan_spec.spl` (5/5), and the seed-pinned
`brace_literal_interp_enum_to_string_spec.spl` (3/3) all pass unmodified.

**The 2026-07-17 empty-swallow sub-case is fixed**: root-caused to the
frontend fragment parser accepting a region whose whole content is itself a
brace literal; `interpolation_fragment_is_brace_literal`
(`src/compiler/10.frontend/core/string_interpolation_expand.spl`, measured
2026-08-17) rejects that class uniformly, and the MIR
`split_interpolation_segments` positional contract is preserved because
malformed regions are literalized (braces doubled) before lowering.

**Status: fixed (verified 2026-11-25).** Two residual *semantics* questions
are explicitly NOT part of this bug and stay with the ratchet entry
`string_interp_malformed_brace_warning_to_error_2026-11-09` (owner decision
needed; both sides are spec-pinned today):

1. *Nested holes inside a malformed region.* The seed's `literalize_braced`
   (`src/compiler_rust/parser/src/expressions/primary/literals.rs:204`,
   spec-pinned 2026-11-05 by `brace_literal_interp_enum_to_string_spec.spl`)
   still interpolates a complete `{hole}` nested inside a malformed region
   (`"{ eye: [0.0, {eye_z}] }"` → `{ eye: [0.0, 9] }`), while the pure-Simple
   compiler keeps the whole region verbatim (spec-pinned 2026-08-17 by
   `interp_brace_literal_fragment_spec.spl`). Same source, different string
   value across compilers; the seed's warning text ("kept as literal text")
   is also imprecise for this shape.
2. *`{margin:0}`-shape (ident + colon + format-spec-looking tail).* The seed
   lexes it as `ExprWithFormat(margin, "0")` (Python f-string parity), so an
   undefined `margin` is a named semantic error; the pure-Simple compiler has
   no format-spec splitting and treats it as a malformed region (warning +
   literal). Syntactically indistinguishable from a legitimate `{x:0}`
   format-spec hole; CSS-authoring guidance (raw strings / `{{ }}`) is already
   documented in `string_interpolation_css_brace_footgun_2026-07-03.md`.

## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Re-verified 2026-09-13 — PARTLY CHANGED, core inconsistency STILL REPRODUCES (left open)

Verification engine: pinned copy of `src/compiler_rust/target/release/simple.exe`
(Simple Language v1.0.1-beta.1, 39,267,840 bytes, sha256 prefix `1b62a1a42755774fc087`,
built 2026-09-13 on this host). Windows 11 / Git Bash, default `run` lane
(seed JIT with interpreter fallback). This is the **Rust bootstrap seed**, not a
deployed pure-Simple self-hosted binary — the self-hosted lane remains unverified
on this host.

Three cases, run on both lanes:

1. A literal with brace groups and NO other placeholder —
   `print("body{font:14px;color:red;}")` — prints verbatim, correct.

2. A literal that mixes a brace group with a real placeholder —
   `print("css {margin:0} then {name}")` — fails:

   ```
   error: semantic: variable `margin` not found
   ```

3. `print("a { b } {name} c")` — same shape, same failure on `b`.

What changed since 2026-07-03: the failure is no longer **silent**. The
brace group is not swallowed and no wrong string is produced — the program
now stops with a named diagnostic on both the seed JIT and tree-walk lanes.
The silent-wrong-output half of this report is therefore gone (measured).

What has NOT changed, and is why this stays open: brace handling inside a
single literal still depends on whether that literal happens to contain
another placeholder. Case 1 and case 2 differ only by the presence of
`{name}` later in the same string, yet the earlier `{...}` is literal in one
and an interpolation in the other. That is the inconsistency the entry asks
to resolve, and it needs the escaping/semantics decision the entry calls for.

**Date:** 2026-07-03
**Severity:** P2 (silent wrong output, not a crash)
**Status:** fixed (verified 2026-11-25 on release/1.0.0 — see top entry; residual nested-hole/format-spec semantics questions tracked under `string_interp_malformed_brace_warning_to_error_2026-11-09`)
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


## 2026-11-09 fix-implemented-verification-pending (staged: escape = hard, malformed brace = warning)

Owner rule: inside a double-quoted literal `{expr}` interpolates, `{{` is a
literal `{`, `}}` is a literal `}`. Seed and self-hosted compilers already
agreed on the escape; the real gap was that a `{...}` that is not a valid
interpolation silently fell back to verbatim text with no diagnostic.

Fix: both compilers keep the verbatim-literal value but now record warning
`W-STR-BRACE-001` carrying the "use `{{` / `}}`" hint.
- Seed: `parser/src/lexer/strings.rs` (`warn_brace`, `BRACE_WARNING_CODE`;
  unmatched `{`, empty `{}`, `{` before a quote/escape) drained into parser
  `error_hints` (Warning level) by `expressions/primary/literals.rs`, which also
  warns for a hole that is not a complete expression (`{ color: red; }`).
- Self-hosted: `string_interpolation_expand.spl` `interpolation_note_malformed_region`
  (called from `parse_string_interpolation_regions` and
  `flat_bridge_build_string_regions`); the MIR `split_interpolation_segments`
  reads the already literalized text, so it needs no change.

Why staged: removing the fallback outright (owner decision) was measured on the
real corpus: 15,033 string literals in `src/**` + `test/**` (44,909 `.spl`
files) would become errors (4,535 unmatched/lone `{`; about 10,500 non-expression
groups: CSS, JSON, awk, `{ return; }`). Raw list: `C:/dev/wt/brace_corpus_scan.log`
(not committed). Promotion to error + codemod is tracked in
`string_interp_malformed_brace_warning_to_error_2026-11-09`.

Left as is: a lone `}` stays accepted (the rule only covers `}}`).

Evidence: seed `cargo test --lib -p simple-parser` 451 passed (new module
`brace_escape_strict` was red before the fix); self-hosted
`test/01_unit/compiler/frontend/string_interp_brace_escape_spec.spl` red
(`interp_brace_warnings_reset` not found) -> green 5/5 with the worktree sources.
