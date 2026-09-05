# `simple check` unknown option false-green

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
