# Duplicate-check invalid mode silently changed analysis

- Status: DUPLICATE of duplicate_check_invalid_enum_value_false_green_2026-07-19.md
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
- **Observed:** `duplicate-check <empty-dir> --mode tokne --format json` silently retained the default semantic mode, emitted a zero-group semantic report, and exited `0`.
- **Cause:** `set_mode` returns the unchanged configuration for values outside `semantic`, `semantic-llm`, `token`, and `cosine`; no pre-scan value validation reports the typo.
- **Required fix:** validate advertised enum-valued options before target scanning and return usage/error exit `2`; cover split and equals forms. Validate `--format` (`text` or `json`) in the same owner to prevent a parallel silent fallback.
- **Constraint:** deferred after the third bounded verify/fix cycle for the parent option-parsing item; do not extend that capped loop.
