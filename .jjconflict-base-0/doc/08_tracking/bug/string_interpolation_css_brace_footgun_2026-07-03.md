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
