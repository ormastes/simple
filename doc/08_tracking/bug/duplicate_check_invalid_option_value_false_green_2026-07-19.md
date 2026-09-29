# Duplicate-check invalid mode silently changed analysis

- **Status:** OPEN; found during final review of unknown-option hardening.
- **Observed:** `duplicate-check <empty-dir> --mode tokne --format json` silently retained the default semantic mode, emitted a zero-group semantic report, and exited `0`.
- **Cause:** `set_mode` returns the unchanged configuration for values outside `semantic`, `semantic-llm`, `token`, and `cosine`; no pre-scan value validation reports the typo.
- **Required fix:** validate advertised enum-valued options before target scanning and return usage/error exit `2`; cover split and equals forms. Validate `--format` (`text` or `json`) in the same owner to prevent a parallel silent fallback.
- **Constraint:** deferred after the third bounded verify/fix cycle for the parent option-parsing item; do not extend that capped loop.
