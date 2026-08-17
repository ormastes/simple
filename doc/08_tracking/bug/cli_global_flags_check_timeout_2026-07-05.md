# CLI Global Flags Check Timeout

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).

## Status

Partially fixed. The focused file check now returns instead of timing out after splitting the global flag parser into smaller helper groups.

## Symptom

`bin/simple check --json src/app/cli/_CliMain/args_and_os_commands.spl` times out before reporting diagnostics. Stage 4 bootstrap traces stop while parsing/checking this module, so redeploy remains blocked before a refreshed pure-Simple CLI binary is produced.

## Evidence

- Full focused check still timed out after 90s on 2026-07-05.
- A standalone `/tmp` repro containing `GlobalFlags`, a stubbed numeric parser, and the real `parse_global_flags` body also timed out with no stdout or stderr.
- Valid cumulative slices through the interpreter-mode and run-config branches passed.
- Adding the backend option pair (`--backend=` / `--backend value`) crossed back into timeout in the bounded repro.
- Mechanical cleanups (`??` removal, unused flag removal, inline-if expansion, wide constructor replacement) did not clear the timeout.
- Splitting core, backend, and limit flag parsing into separate helpers made `bin/simple check src/app/cli/_CliMain/args_and_os_commands.spl` reach file-level `OK` in 14 seconds. The command still exits nonzero in the repo hygiene gate with `simple: seed sibling not found, skipping delegation: /usr/bin/simple_seed`.
- Added a repo-local `bin/simple_seed` fallback in `src/app/io/cli_ops.spl` and a source regression in `test/01_unit/app/io/cli_argv0_resolution_spec.spl`. The currently deployed binary still contains the old delegation path, so the spec cannot run until this source fix is rebuilt/redeployed.
- On 2026-07-24, a cached pure-Simple Stage 4 `native-build` for the repaired
  test-runner JSON lane hit its 1,800-second hard cap with no candidate
  artifact. Phase tracing loaded the 630-file closure in 202 seconds, then
  stopped after:

  ```text
  +259736ms phase2:parse:file:start src/app/cli/main.spl chars=773
  +266680ms phase2:parse:file:done src/app/cli/main.spl
  +266795ms phase2:parse:file:start src/app/cli/_CliMain/args_and_os_commands.spl chars=11666
  ```

  The process remained CPU-active and memory-stable until timeout. This
  independently reproduces the same file-local blocker on the production
  Stage 4 link path; retrying the JSON contract cannot qualify the repair
  until this parser/checker defect is fixed.

## Next Step

Rebuild/redeploy the pure-Simple CLI so the repo-local seed fallback is present in the running binary, then rerun the focused check without `SIMPLE_BOOTSTRAP_DRIVER`.
