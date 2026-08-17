# Bootstrap stage2: silent exit-1 with a 0-byte stage2-native-build.log

- **Date:** 2026-08-17
- **Status:** MITIGATED (diagnostic added); root output-buffering defect still open
- **Component:** `scripts/bootstrap/bootstrap-from-scratch.sh`, `native-build` output behavior

## Symptom
A full-bootstrap run in `/mnt/data/worktrees/simple-boot-snap` had stage2 exit 1
with `stage2-native-build.log` present but **0 bytes** — no error text anywhere.
Evidence: `build/bootstrap/stage3/x86_64-unknown-linux-gnu/stage2-command.transcript`
(schema `simple-bootstrap-command-transcript-v2`) plus the empty log in the same run.

## Root cause analysis (replay evidence)
Replayed the transcript's exact command against the phase-1 snapshot binary
`build/phase_snapshots/phase1_1786935122/simple` in a scratch dir with the same
`env -i HOME=... PATH=... TMPDIR=... LC_ALL=C LANG=C` sandbox plus all
`explicit-env` records:

- `--version` and `native-build --help` under the sandbox env: exit 0, normal
  output. **The sandbox env (restricted PATH/HOME/TMPDIR) does NOT break the
  seed.**
- The full `native-build ... --entry src/app/cli/bootstrap_main.spl` command ran
  90s and then 580s under `timeout` doing real CPU work with a **0-byte log the
  entire time** — `native-build` writes nothing to a non-tty stdout/stderr until
  completion or a flushed error. `SIMPLE_BUILD_PROGRESS_EVENTS` is a file path
  (empty in non-resumable runs), not a verbosity flag, so no progress evidence
  exists either.

Therefore a 0-byte log + exit 1 means the compiler ran and died mid-build
without flushing anything — OR the transcribed-run wrapper
(`bootstrap_stage3_run_transcribed`, scripts/check/lib/bootstrap-stage3/command-snapshot.shs)
`return 1`-ed on a precondition **before** executing anything (in which case the
log is never created at all), or returned 125 on post-run transcript
verification. The three cases were previously indistinguishable and all silent.

## Fix (additive, does not fight the env hardening)
`bootstrap-from-scratch.sh` now prints a diagnostic block when
`stage2_status != 0` and the log is empty, distinguishing:
- log never created → wrapper precondition refusal (pre-exec)
- log created but 0 bytes → compiler died unflushed; points at the transcript
  for interactive replay
- exit 125 → wrapper post-run transcript/env verification failure

## Still open
`native-build` should flush progress/diagnostics to a non-tty (line-buffered
stderr at minimum) so a mid-build death leaves evidence. Tracked separately from
this script mitigation.
