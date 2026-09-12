# Duplicate-check invalid mode silently changed analysis

- **Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)
- **Observed:** `duplicate-check <empty-dir> --mode tokne --format json` silently retained the default semantic mode, emitted a zero-group semantic report, and exited `0`.
- **Cause:** `set_mode` returns the unchanged configuration for values outside `semantic`, `semantic-llm`, `token`, and `cosine`; no pre-scan value validation reports the typo.
- **Required fix:** validate advertised enum-valued options before target scanning and return usage/error exit `2`; cover split and equals forms. Validate `--format` (`text` or `json`) in the same owner to prevent a parallel silent fallback.
- **Constraint:** deferred after the third bounded verify/fix cycle for the parent option-parsing item; do not extend that capped loop.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
