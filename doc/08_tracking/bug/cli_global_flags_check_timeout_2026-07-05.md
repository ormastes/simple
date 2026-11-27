# CLI Global Flags Check Timeout
## Resolved 2026-11-25 — check on the named module completes in ~31s

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Status

Resolved (verified 2026-11-25, see bottom section).

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


## Verification 2026-11-25 — CLOSED (symptom no longer reproduces)

On worktree `work/p2w1-aa-20261125` (release/1.0.0 HEAD `38265c7f249`) with
the pinned tracked seed `bin/simple.exe` (38,403,072 bytes, Rust seed
v1.0.0-rc.1):

```
SIMPLE_LIB=src bin/simple.exe check src/app/cli/_CliMain/args_and_os_commands.spl
```

completed in ~31 s wall-clock with exit 0, emitting ordinary lint warnings
(`export use *` style warnings from the import graph) instead of hanging.
The filed symptom — "times out before reporting diagnostics", still timing
out after 90 s on 2026-07-05 — no longer reproduces on the current seed; the
check lane walks the module and its import graph and reports diagnostics.
