# CLI Global Flags Check Timeout
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Status

Open.

## Symptom

`bin/simple check --json src/app/cli/_CliMain/args_and_os_commands.spl` times out before reporting diagnostics. Stage 4 bootstrap traces stop while parsing/checking this module, so redeploy remains blocked before a refreshed pure-Simple CLI binary is produced.

## Evidence

- Full focused check still timed out after 90s on 2026-07-05.
- A standalone `/tmp` repro containing `GlobalFlags`, a stubbed numeric parser, and the real `parse_global_flags` body also timed out with no stdout or stderr.
- Valid cumulative slices through the interpreter-mode and run-config branches passed.
- Adding the backend option pair (`--backend=` / `--backend value`) crossed back into timeout in the bounded repro.
- Mechanical cleanups (`??` removal, unused flag removal, inline-if expansion, wide constructor replacement) did not clear the timeout.

## Next Step

Minimize the backend-branch repro, then fix the parser/checker path or replace the manual flag parser with the already-planned `cli` declaration once that language support is available.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
