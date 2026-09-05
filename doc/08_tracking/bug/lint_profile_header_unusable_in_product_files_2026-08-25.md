# `@lint_profile(critical)` file header cannot be placed in any product file

**Date:** 2026-08-25  **Severity:** medium  **Area:** parser / lint tier selection
**Binary:** `bin/release/x86_64-unknown-linux-gnu/simple` (Rust seed)

## Symptom
`doc/07_guide/language/strictness_tiers.md` documents `@lint_profile(critical)` as a
"file-header attribute (top of file, before defs)". Placing it in a real module fails in
every position:

| placement | result |
|---|---|
| line 1, before `use` | `parse: Unexpected token: expected Fn, found Use` |
| before a top-level `val` | `parse: Unexpected token: expected Fn, found Val` |
| before the first `fn` (parses) | when the module is IMPORTED: `semantic: unknown decorator `@lint_profile` on function ...` |
| before a `struct` | parses, but the lint header scanner (`_LintMain/config_and_model.spl:515-540`) already works; runtime import untested for structs |

Census: zero product files under `src/` carry the header; the only users are lint
fixtures. Reproduced while bringing `src/lib/scv/**` under the `critical` tier: inserting the
header before the first `fn` of `core.spl` broke every SCV spec with the decorator error.

## Impact
The precedence-1 tier selector is unusable outside fixtures. Tier enforcement must go through
`--profile=critical` (precedence 2) in a gate script, which is what
`scripts/check/check-scv-mission-critical.shs` does.

## Expected
Either the parser accepts a standalone module-level `@lint_profile(...)` attribute (before
`use`/`val`), or the semantic pass whitelists `@lint_profile` as a file-scope, non-function
attribute. Regression spec to add with the fix: a module carrying the header on line 1 must
import cleanly and `simple lint` must report the `critical` tier for it.
