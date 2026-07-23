# Fix CLI invalid option can write

- **Status:** option hardening fixed in source; runtime qualification blocked.
- **Observed:** `simple fix file.spl --dry-run=true` silently ignored the malformed option, then applied safe fixes because write mode is the default.
- **Fix:** both active pure-Simple fix CLI owners now reject unknown options and empty `--fix-id=` with exit 2 before reading or writing files.
- **Regression:** the lightweight and production-owner contracts (`fix_cli_option_validation_contract_check.spl` and `fix_production_cli_option_validation_contract_check.spl`) each prove malformed/unknown options leave a fixable fixture unchanged, while exact `--dry-run --fix-all --fix-id=ID` remains accepted and non-mutating.
- **Qualification blocker (2026-07-23):** the final bounded run reached a real lazy imported class-static dispatch failure, `unknown static method apply_to_disk on class FixApplicator`, in each isolated owner. `apply_fixes_to_disk` now owns the write body, and the legacy static method only delegates for compatibility; all active owners use the module facade. Run the unchanged focused contracts in a fresh session before crediting runtime evidence.
