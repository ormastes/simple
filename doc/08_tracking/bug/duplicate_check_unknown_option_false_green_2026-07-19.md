# Duplicate-check unknown option scanned its value

- **Status:** FIXED in source; current Stage 4 qualification remains pending.
- **Observed:** `duplicate-check --bogus <empty-dir> --mode token --format json` treated `<empty-dir>` as the required target, scanned it, emitted zero groups, and exited `0`.
- **Cause:** target selection skipped every dash-prefixed argument, while the later option parser silently ignored unknown flags.
- **Fix:** the shared target-argument owner now accepts exact known switches or nonempty known value options, validates split option values, requires exactly one positional target, scans the full argv before returning it, and rejects malformed or unknown options before any filesystem scan.
- **Regression:** `target_path_args_spec.spl` covers unknown and malformed split/equal options plus extra targets; `duplicate_check_contract_spec.spl` proves the real source CLI exits `2` with usage for unknown and malformed switches.
- **Residual:** known options with invalid enum values are a separate open case; for example, `--mode tokne` still falls back to semantic analysis instead of rejecting the typo.
