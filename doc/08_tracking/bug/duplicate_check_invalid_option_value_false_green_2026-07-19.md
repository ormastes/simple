# Duplicate-check invalid mode silently changed analysis

- **Status:** OPEN; found during final review of unknown-option hardening.
- **Observed:** `duplicate-check <empty-dir> --mode tokne --format json` silently retained the default semantic mode, emitted a zero-group semantic report, and exited `0`.
- **Cause:** `set_mode` returns the unchanged configuration for values outside `semantic`, `semantic-llm`, `token`, and `cosine`; no pre-scan value validation reports the typo.
- **Required fix:** validate advertised enum-valued options before target scanning and return usage/error exit `2`; cover split and equals forms. Validate `--format` (`text` or `json`) in the same owner to prevent a parallel silent fallback.
- **Constraint:** deferred after the third bounded verify/fix cycle for the parent option-parsing item; do not extend that capped loop.

## Resolution (2026-11-08)

**Status:** FIX IMPLEMENTED / VERIFICATION PENDING.

`duplicate_check/main.spl` now preserves invalid `--mode` values through
`apply_analysis_mode`, so checked parsing rejects them instead of silently
restoring the previous mode. Existing pre-scan validation rejects invalid mode
and format values with usage and exit `2`. Unit coverage exercises split and
equals forms, all four valid modes, and `text`/`json`; the system contract
checks exit `2` and usage for invalid mode/format in both forms.

The new Simple tests remain unexecuted in this lane: deployed binaries are
bootstrap-only, and the current full-CLI build stops on the pre-existing
`windows_image_owner.spl` parse error. `git diff --check` passes.
