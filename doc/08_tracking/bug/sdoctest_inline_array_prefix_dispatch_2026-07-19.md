# Sdoctest inline arrays used a nonexistent prefix helper

- **Status:** fixed; focused interpreter regression passed
- **Observed:** parsing `ignore.paths` or `ignore.tags` could fail at `starts_with(inner, "[")`.
- **Cause:** the parser used a free-function spelling while text prefix checks are canonical instance methods.
- **Fix:** route through `inner.starts_with("[")` in the shared nogc-sync implementation re-exported by the other GC families.
- **Regression:** the async facade spec parses bracketed ignore path/tag arrays and checks their exact values.
