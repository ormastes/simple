# Char Literal Policy

> `'x'` is one Unicode scalar; raw, interpolated and triple-quoted strings behave as documented.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language |
| Requirement | ADR-005 Decision.2 and Lexer; `doc/07_guide/quick_reference/syntax_quick_reference.md` |
| Source | `test/03_system/language/policy/char_literal_spec.spl`, `char_literal_in_dev_spec.spl` |
| Generator | hand-written (spipe-docgen not run) |

## Scenarios

| # | Scenario | Status |
|---|----------|--------|
| 1 | `'x'` has the code point of x | passing |
| 2 | `r"a\nb"` keeps backslashes verbatim | passing |
| 3 | `"v={k + 1}"` interpolates | passing |
| 4 | `"""..."""` keeps newlines | passing |
| 5 | `"\u{..}"` string escape is one code point | passing |
| 6 | Literal forms agree on interpreter and JIT | passing |
| 7 | `'\u{e9}'`, `'\n'`, `'\''` each count as one char | in-development |
| 8 | Decomposed e + U+0301 literal rejected with a diagnostic | in-development |
| 9 | ZWJ emoji literal rejected with a diagnostic | in-development |
