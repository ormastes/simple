# CLI Global Flags Check Timeout

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

Minimize the backend-branch repro, then fix the parser/checker path or replace the manual flag parser with the already-planned `cli` declaration once that language support is available.
