# Duplicate-check invalid mode silently changed analysis

- **Status:** FIXED (2026-11-11, lane ne7); found during final review of unknown-option hardening.
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

## Verification addendum (2026-11-11, lane ne7)

**Status: FIXED — verified on fresh seed 46fe8f6b6def (2026-11-11).**

The 2026-11-08 fix (`0247364fa1ad`) implemented the validation but its new
tests were never executed (the resolution itself records
"VERIFICATION PENDING"). On this lane's fresh seed
(`SIMPLE_LIB=src SIMPLE_BINARY=$PWD/bin/simple.exe ... test ... --mode=interpreter --no-cache`,
label seed-smoke) the tests first errored at compile: the spec-imported
functions were still module-private (`error: semantic: private fn
'parse_args_checked' ... not visible`), a gap inside the fix commit itself.

Repair in this lane (paired with the already-committed tests): marked the
spec-imported functions `pub` —
`src/compiler/90.tools/duplicate_check/main.spl`
(`collect_command_args`, `parse_args`, `parse_args_checked`),
`src/compiler/90.tools/duplicate_check/config.spl`
(`default_config`, `analysis_mode`, `target_path_from_args`),
`src/compiler/90.tools/duplicate_check/formatter.spl`
(`summarize_duplicate_groups`, `duplicate_lines_per_block`,
`format_score_hundredths`, `format_ratio_tenths`).

Seed-smoke results (all PASS):

- `test/01_unit/app/duplicate_check/duplicate_check_spec.spl` — 7/7
- `test/01_unit/app/duplicate_check/target_path_args_spec.spl` — 6/6
- `test/03_system/app/cli/duplicate_check_contract_spec.spl` — 3/3
  (exit 2 + usage for invalid mode/format in split and equals forms)
