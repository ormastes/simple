# Short Grammar Migration Audit

Date: 2026-05-27

## Scope

Audit of the active short-grammar migration and compatibility work:

- migrate safe explicit single-expression lambdas to short grammar
- improve short-grammar compatibility in parser/interpreter paths
- improve fixer coverage for safe and unsafe rewrites
- verify the graphics optimization plugin in interpreter and native modes

## Evidence

Current focused verification passed:

- `test/feature/language/placeholder_lambda_spec.spl`: 47 passed, 0 failed
- `test/unit/compiler_core/parser/short_grammar_interpreter_spec.spl`: 19 passed, 0 failed
- `test/unit/compiler_core/parser/short_grammar_native_spec.spl`: 1 passed, 0 failed
- `test/unit/app/fix/short_grammar_fix_spec.spl`: 64 passed, 0 failed
- `test/perf/graphics_2d/optimization_plugin_spec.spl --mode=interpreter`: 14 passed, 0 failed
- `test/perf/graphics_2d/optimization_plugin_spec.spl --mode=native`: 1 passed, 0 failed
- Rust parser expression tests: 27 passed, 0 failed
- Rust parser placeholder unit tests: 3 passed, 0 failed
- Focused `simple check` passed for short-grammar parser/fixer/spec/example files.

## Compatibility Fixed

- Placeholder traversal now covers f-string interpolation and tuple indexes.
- Source-level parser coverage verifies tuple placeholder interpolation.
- `??` fallback parsing now accepts a full expression, so `_ ?? -1 * 100`
  evaluates as `_ ?? (-1 * 100)`.
- Indexed placeholders in feature specs now run in interpreter mode.

## Tooling Status

The short-grammar fixer now covers safe conversions for:

- method references
- direct function references
- placeholder transforms and predicates
- indexed predicates with param-free index expressions
- interpolated string callbacks
- tuple destructuring callback rewrites where supported
- ignored named parameters rewritten to `\_:`

The fixer explicitly does not rewrite already-wildcard constant callbacks such
as `\_: "literal"` or `\_: true`, because `\_:` is the documented compact form
when the argument is ignored but the higher-order call still needs a function.

## Remaining Classified Hits

The remaining simple explicit-lambda scan hits are classified as:

- explanatory desugaring text in placeholder-lambda documentation
- already-minimized `\_:` constant or wildcard callbacks

The constant-callback shorthand decision is documented in:

- `doc/08_tracking/bug/short_grammar_constant_callback_form_missing_2026-05-27.md`

## Conclusion

The implemented migration and compatibility work is verified for the focused
short-grammar surface and optimizer plugin. The remaining scan hits are either
explanatory text or canonical `\_:` ignored-argument callbacks.
