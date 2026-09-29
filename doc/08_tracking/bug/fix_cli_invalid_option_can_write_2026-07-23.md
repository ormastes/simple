# Fix CLI invalid option can write

- **Status:** source fixed; focused bootstrap-interpreter contracts pass; fresh pure-Simple qualification blocked.
- **Observed:** `simple fix file.spl --dry-run=true` silently ignored the malformed option, then applied safe fixes because write mode is the default.
- **Fix:** both active pure-Simple fix CLI owners now reject unknown options and empty `--fix-id=` with exit 2 before reading or writing files.
- **Regression:** the lightweight and production-owner contracts (`fix_cli_option_validation_contract_check.spl` and `fix_production_cli_option_validation_contract_check.spl`) each prove malformed/unknown options leave a fixable fixture unchanged, while exact `--dry-run --fix-all --fix-id=ID` remains accepted and non-mutating.
- **Evidence and remaining blocker (2026-07-23):** both unchanged owner contracts pass after `apply_fixes_to_disk` became the single write-body owner and the legacy static method became a compatibility delegate. The retained pure-Simple binary still crashes with the separately tracked stale `rt_env_set` ABI before either contract executes; deploy a frontend-admitted candidate before crediting pure-Simple or Stage 4 evidence.
