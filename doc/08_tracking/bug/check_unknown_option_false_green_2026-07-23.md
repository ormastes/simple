# `simple check` unknown option false-green

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

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

## Fresh runtime qualification 2026-08-17 — NOT REPRODUCED, closing

The "fresh Stage 4 runtime evidence remains pending" gate above is now
satisfied against the deployed `bin/simple`. Classified by CONTENT, not by
commit ancestry (SHA ancestry is unsound in this repo).

Source evidence: `src/app/check/main.spl:275-280` calls
`check_option_error(args)` and returns non-zero before any file discovery.
`src/app/check/check_options.spl` ends its scan loop with an explicit
`if arg.starts_with("-"): return "unknown option: {arg}"` catch-all, so an
unrecognised dash-argument cannot fall through to the file collector.

Runtime evidence (fixture: a single well-formed `ok.spl`):

    $ bin/simple check --bogus-option .../ok.spl
    ERROR: unknown option: --bogus-option
    rc=2

Exit code read into `rc` on the line after the command, never through a pipe.
The command errors and exits non-zero; it does not accept the option and it
does not report green. The false-green defect does not reproduce.

Residual, filed here rather than silently normalised: the observed exit code
is **2**, while `main()` in `src/app/check/main.spl:280` returns **1** for the
option-rejection path. The verdict (hard failure) is correct and the bug class
is dead either way, but the 1-vs-2 discrepancy means some outer wrapper is
remapping the status. That is an exit-code-fidelity question, not a false
green, and is out of scope for this doc.

Status: NOT REPRODUCED / already fixed in source. No code change made.

## Verification 2026-08-17 (wave_00 w0001/app_1) — CLOSE, fix confirmed by content AND live run

Source is fail-closed. `src/app/check/check_options.spl:65-66`:

```
        if arg.starts_with("-"):
            return "unknown option: {arg}"
```

and `src/app/check/main.spl:275-280`:

```
    val option_error = check_option_error(args)
    if option_error != "":
        print "ERROR: {option_error}"
        # Option rejection is exit 1 across every command that shares the
        # log-mode/progress option surface (brief, bug-gen, cache, cli, mcp).
        return 1
```

Live run, `nice -n 19 bin/simple check --definitely-not-a-real-option src/app/dashboard/main.spl`
(rc captured on the line after the command, not through a pipe):

```
ERROR: unknown option: --definitely-not-a-real-option
rc=2
```

Non-zero exit with an explicit error. The false green is gone. Closing.
