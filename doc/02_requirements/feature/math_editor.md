# LibreOffice Math Requirements

## Scope

Math is the office-suite equation substrate exposed through
`app.office.math_editor` and the IDE Office catalog. This slice keeps the model
pure MathML rendering while adding structured equation forms used by
LibreOffice Math-style editing.

## Requirements

- MATH-001: Flat expressions render deterministic MathML using `<mi>`, `<mn>`,
  and `<mo>` token elements.
- MATH-002: XML-sensitive token text is escaped before entering MathML output.
- MATH-003: `frac(a, b)` shorthand renders a MathML `<mfrac>` through the public
  `math_to_mathml` renderer.
- MATH-004: Compound fraction arguments render as nested `<mrow>` content.
- MATH-005: Malformed fraction shorthand falls back to deterministic flat token
  rendering without crashing.
- MATH-006: Structured helpers render fraction, superscript, subscript, square
  root, and fenced-group MathML forms.
- MATH-007: Core arithmetic operators render with deterministic precedence:
  exponent, multiplication/division, then addition/subtraction.
- MATH-008: Parenthesized groups alter precedence in the rendered MathML.
- MATH-009: Checked rendering reports deterministic failure reasons for empty
  expressions, unbalanced parentheses, malformed operator positions, malformed
  fraction arity, missing square-root arguments, and token-limit rejection while
  still returning fallback MathML.

## Out of Scope

CAS evaluation, equation editing UI commands, and LaTeX/LibreOffice formula
import remain follow-up slices.
