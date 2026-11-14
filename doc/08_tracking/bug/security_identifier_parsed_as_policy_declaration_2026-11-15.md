# `security` statement always parsed as a policy declaration (2026-11-15)

**Status:** FIXED (requires rebuilt seed)

## Symptom
`security.policy_bound = true` failed in the Rust seed with
`expected identifier, found Dot`.

## Root cause
`src/compiler_rust/parser/src/parser_impl/core.rs` dispatched every statement
whose first token was the identifier `security` to `parse_security_policy`
unless the next token was `gate`.

## Fix
Contextual: declaration only for `security:`, `security <ident>:` or
`security gate ...`; otherwise `parse_expression_or_assignment`. The
pure-Simple parser (`src/compiler/10.frontend`) has no `security` declaration
form, so it already treats `security` as an identifier (no parity change).

Same defect class, same dispatch: `sandbox` and `ui_policy` statements were
unconditionally declarations; now only `<kw> <Name>:`.

Regression: `test/01_unit/compiler/parser_security_contextual_keyword_spec.spl`
and Rust test `security_contextual_identifier_statement`.
Generalization: `test/01_unit/compiler/parser_policy_soft_keyword_generalization_spec.spl`
and Rust test `sandbox_and_ui_policy_contextual_identifier_statement`.
