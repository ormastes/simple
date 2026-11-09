# Seed reports semantic errors with no file:line:col

- **Priority**: P3
- **Duplicate (2026-11-09)**: closed as resolved-duplicate; tracked by `seed_semantic_error_missing_position_2026-11-09` (kept).
- **Status**: open
- **Split out**: 2026-11-09, by owner decision, from `seed_optional_query_comparison_divergence_2026-08-16.md` (was Divergence C there).

## Divergence C — Seed reports semantic errors with no position information

Both divergences A and B presented as runtime mysteries (nil pointer dereference, type mismatch with no source location) because the seed's semantic error reporting omits file and line number information.

Error format under seed:
```
error: semantic: <error message only>
```

Error format under self-hosted:
```
<file>:<line>:<col>: error: semantic: <error message>
```

This lack of context makes seed-vs-self-hosted discrepancies hard to localize. A semantic error can be traced only by runtime behavior (where it manifests), not by its origin.

**Diagnosability gap:** The seed should report error position on all semantic failures.

**Status:** Open; no immediate fix planned. Workaround: use the self-hosted compiler for debugging semantic errors, not the seed.
