# Bug: string interpolation silently swallows CSS-like braces inconsistently

- **Date:** 2026-07-03
- **Severity:** low-medium (confusing error, content-dependent)
- **Area:** lexer/parser string interpolation

## Symptom
In a string literal, `"{color:#ffffff}"` is parsed as INTERPOLATION of
variable `color` (with `#ffffff` treated as a format spec?) and fails at
run time with `semantic: variable 'color' not found`, while
`"{position:absolute;background:#1e293b}"` stays literal. Whether a CSS
rule body interpolates depends on whether its prefix happens to parse as
an expression — silent, content-dependent, and the error points nowhere.

## Repro
`val s = "<style>.t{color:#ffffff}</style>"` → semantic error at use.
`val s = ".t" + "{" + "color:#ffffff" + "}"` → works.

## Expected
Either a consistent rule (always interpolate `{...}` and require escaping,
with a parse-time error pointing at the literal) or reject ambiguous
interpolations at parse time with location info. Current behavior produces
a location-less runtime semantic error naming a variable the user never
wrote as code.

## 2026-08-07 re-verification: still open; confirmed workaround

Re-probed at tip with a minimal file
(`.t{color:#ffffff}` / `body {color: red}`) across three engines/harnesses:

- `bin/simple run` (seed/native default): the word-value case
  (`{color: red}`) happens to fall back to literal text (content-dependent,
  not guaranteed). The hex-color case (`{color:#ffffff}`) does **not**
  error — it silently corrupts with no diagnostic: `print` of
  `".t{color:#ffffff}"` emitted `.t0` instead of the CSS text. In the probe
  that found this, the very next statement's `0` (a following expression in
  the same function) was absorbed into that corrupted output — i.e. the
  corruption is not always contained to the single offending `print` call.
- `SIMPLE_EXECUTION_MODE=interpret`: hard-fails on the hex-color case with
  the same location-less `semantic: variable 'color' not found` as the
  original filing.
- `bin/simple test` (hard-defaults to the tree-walk interpreter per
  `.claude/rules/testing.md`): same hard-fail — and notably this hits even
  an UNESCAPED `{prop:val}`-shaped literal written only as an
  `expect(...).to_equal("...")` expected value, independent of what's under
  test. Confirmed via a throwaway diagnostic spec:
  `expect(v).to_equal(".t{color:#ffffff}")` failed to parse even though `v`
  held the byte-correct string.

**Preferred fix, confirmed working in all three engines/harnesses above: a
raw string literal.** The grammar already has one — see
`doc/07_guide/quick_reference/syntax_quick_reference.md` "Raw Strings (No
Interpolation)" — so no new lexer/parser grammar is needed here.
Single-quoted `'...'` strings never interpolate; `r"..."` (double-quote,
r-prefixed) also works and was verified byte-correct in `bin/simple run`,
`SIMPLE_EXECUTION_MODE=interpret`, and `bin/simple test`, including as an
`expect(...).to_equal(...)` expected-value literal. Note: `r'...'`
(single-quote WITH the `r` prefix) is NOT supported — it parses as a call to
an undefined function `r` and hard-errors (`function 'r' not found`); that
combination is redundant anyway since plain `'...'` is already raw.

**Secondary workaround, also confirmed working in all three
engines/harnesses:** double the braces (`{{`/`}}`) inside an interpolated
(double-quoted) string, exactly as documented in
`interp_brace_literal_collides_with_string_interpolation_2026-07-03.md`'s
2026-07-17 fix. `.t{{color:#ffffff}}` renders as `.t{color:#ffffff}`
byte-for-byte in every engine tested. Useful only when a raw string isn't a
good fit (e.g. the literal also needs real interpolation alongside literal
braces); prefer the raw-string form otherwise.

Spec demonstrating both confirmed fixes, using independent oracles (exact
length pin + cross-form equality between two independently-lexed forms, so
a regression in the collapse/raw-passthrough mechanism can't silently pass
by comparing a literal against an identically-written literal):
`test/01_unit/bugs/string_interp_css_brace_footgun_spec.spl`
(`Results: 6 total, 6 passed, 0 failed`).

No occurrences of the broken unescaped `{ident:#hex}`-shaped pattern were
found in `src/lib/common/ui` via
`/usr/bin/grep -rn '"[^"]*{[a-zA-Z_][a-zA-Z0-9_]*:#' src/lib/common/ui`
(zero matches). This grep was verified non-vacuous by planting a known-
positive line (`"body {color:#abcdef}"`) in a scratch file and confirming
the same pattern matches it — the search itself is not silently blind.
(Caveat: the system's aliased `grep`, actually `ugrep`, silently failed to
match this same known-positive combined pattern without `-P`; `/usr/bin/grep`
was used explicitly for this check — see
`.claude/memory/reference_positive_capability_probe_for_binary_identity.md`
for the general pitfall.) This only rules out this one narrow brace-shape;
it is not proof no other CSS/JSON-brace-literal footgun exists elsewhere in
the tree. Existing UI/CSS-generating code does not hit this specific
footgun today, but the raw-string or `{{ }}` requirement should be called
out for any future code that builds CSS/JSON-shaped text via plain
double-quoted string literals.
