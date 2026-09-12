# spipe-docgen ignored unknown options and wrote default output — 2026-07-23

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

- **Impact:** a misspelled output option could report success while generating
  into canonical `doc/06_spec` instead of the requested isolated directory.
- **Root cause:** the pure-Simple argument loop discarded unrecognized
  dash-prefixed arguments.
- **Fix:** reject every unrecognized option before filesystem generation.
- **Regression:** `spipe_docgen_scenario_body_spec.spl` pins `--outpt` to a
  nonzero exit with no default generated manual. The temporary seed runner
  reported `no examples executed`; run this unchanged scenario with the next
  admitted pure-Simple runner before crediting runtime qualification.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
