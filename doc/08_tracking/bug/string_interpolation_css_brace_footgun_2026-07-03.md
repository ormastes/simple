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

## 2026-08-08 re-verification: still live; judged design-consequence + diagnostic gap, not a grammar defect

Re-ran the spec (`test/01_unit/bugs/string_interp_css_brace_footgun_spec.spl`):
`Results: 6 total, 6 passed, 0 failed`, rc=0 — unchanged, still correct, left
as-is.

Re-probed the two failure modes with fresh minimal repros:
- `bin/simple run` on `"body {color:#fff}"`: **silent corruption, no
  diagnostic at all**, rc=0. `print(s)` emits `body 0` instead of the source
  text — the `{color:#fff}` span is swallowed and replaced by the evaluated
  (and wrong) result of treating `color:#fff` as some kind of
  identifier/format-spec parse, with no error surfaced anywhere.
- `SIMPLE_EXECUTION_MODE=interpret` on the same literal: hard-fails, rc=1,
  with only `error: semantic: variable `color` not found` printed — no
  file:line, no mention that the offending token came from inside a string
  literal.
- A JSON-shaped literal (`"{\"key\": \"value\"}"`) and an unclosed single
  brace (`"left { brace only"`) both pass through as literal text with no
  error in `bin/simple run` — confirms the bug doc's original
  "content-dependent" characterization; there is no reliable rule for which
  `{...}` shapes survive unescaped.

**An escape mechanism exists and works**: raw strings (`'...'`, `r"..."`)
and the `{{`/`}}` doubled-brace escape are both confirmed correct (this is
exactly what the passing spec pins). This makes Simple's design consistent
with Python f-strings / Rust `format!` / C# interpolated strings, all of
which treat `{}` specially in interpolating strings and require an escape —
**this is a normal, defensible language design, not a grammar gap**. No
grammar change is recommended.

**The real defect is the diagnostic**, and it is worse than it looks. Traced
the interpret-mode error to
`src/compiler_rust/compiler/src/interpreter/expr/literals.rs:338-363`: the
Rust seed's undefined-variable path already builds a rich `ErrorContext` —
error code `codes::UNDEFINED_VARIABLE` (E1001), a `with_help("check that the
variable is defined and in scope")`, a "did you mean `X`?" typo suggestion,
and (when ≤5 names are in scope) a `with_note("available variables: ...")`
listing. **None of that reaches the terminal** — the CLI print path for this
error only ever emits `error: semantic: variable `color` not found`, no
code, no help, no note, no location. So there are two independent gaps
stacked: (1) the error has no way to say "this identifier came from inside a
string literal, did you mean to escape `{`?", and (2) even the generic
help/note/code payload it does construct is silently dropped before
printing. This is Rust-seed interpreter code
(`src/compiler_rust/compiler/src/interpreter/`), not reachable from `.spl`,
so per repo rule ("Fix .spl not Rust") no code change was made here.

**Recommendation:**
1. Documentation fix, done in this pass: added a "Literal Braces in an
   Interpolated String (CSS/JSON footgun)" subsection to
   `doc/07_guide/quick_reference/syntax_quick_reference.md` (under
   "Strings") covering both confirmed escapes and both failure modes, since
   the existing "Raw Strings" section didn't call out the interpolation
   collision at all and never mentioned the `{{`/`}}` escape.
2. File a follow-up feature request (not implemented here — Rust-seed
   interpreter/CLI error-formatting change, out of scope for a `.spl`-only
   fix and for this lane's effort budget) to: (a) surface the existing
   `ErrorContext` help/note/code at the CLI print site instead of dropping
   it, and (b) special-case the string-interpolation undefined-variable path
   to name the enclosing string literal and suggest the `{{`/raw-string
   escape. That would turn a location-less, misleading "variable not found"
   into an actionable message without any grammar change.
3. The `bin/simple run` silent-corruption case (no diagnostic, no error, wrong
   output) is the more severe of the two failure modes and is not touched by
   the interpret-mode fix above, since it doesn't go through this error path
   at all — it deserves its own investigation into why the JIT/native lane
   swallows the span instead of erroring or interpolating consistently with
   the interpreter. Left open, not investigated further in this pass.

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
