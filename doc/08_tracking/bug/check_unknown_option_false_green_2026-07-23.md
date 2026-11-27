# `simple check` unknown option false-green
## Closed 2026-09-16 — source fixed, check_option_error contract spec passes (Stage 4 qual pending)

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

**Status:** source fixed; focused bootstrap contract passes; fresh Stage 4 qualification remains pending.

`simple check --typo file.spl` previously ignored `--typo`, checked `file.spl`,
and could return zero. A misspelled safety or output option could therefore make
automation report a successful check with different behavior than requested.

Both the normal worker and lightweight entry now share `check_option_error`,
which rejects unknown, empty, option-looking, and invalid-domain options with
exit code 2 before file discovery. It accepts only canonical `log-mode`
(`human|llm|json`), `surface` (`stdout|tui`), and `progress`
(`summary|count|dot|none`) values in split or equals forms.
`test/01_unit/app/check_cli_option_validation_contract_check.spl` covers the
fail-closed and accepted forms and passes through the temporary bootstrap
interpreter. Fresh Stage 4 runtime evidence remains pending.


## Re-verification 2026-11-25 (fleet lane p2w1-ai, worktree wt-p2w1-ai, release/1.0.0 HEAD 50adb6f42ce)

Closed status confirmed with fresh runtime evidence:

- Fix present in source: `check_option_error` is defined in
  `src/app/cli/check_options.spl` and enforced by both the normal worker
  (`src/app/cli/check.spl:22,316`) and the lightweight entry
  (`src/app/cli/check_entry.spl:12,315`).
- Contract check executed:
  `SIMPLE_LIB=src bin/simple.exe run test/01_unit/app/check_cli_option_validation_contract_check.spl`
  (Windows host, pinned seed v1.0.0-rc.1) printed
  `PASS: check rejects invalid options before file discovery`.

The closure note's "fresh Stage 4 qualification remains pending" caveat is
unaffected by this re-verification; the source-level fix and its contract
spec are confirmed green.
