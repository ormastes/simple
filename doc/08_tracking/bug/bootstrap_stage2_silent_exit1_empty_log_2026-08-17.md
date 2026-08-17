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

## 2026-08-17 triage — mitigation stands; root defect not re-verifiable in this lane

Left OPEN as filed. The diagnostic mitigation is in place; the root
output-buffering defect (stage2 exiting 1 with a 0-byte
`stage2-native-build.log`) can only be re-observed by running a full bootstrap,
which this lane is explicitly forbidden to do (never build the main compiler,
never touch `/mnt/data/worktrees/simple-boot-snap`).

Corroborating same-family evidence gathered today without a bootstrap, worth
recording because it shows the symptom is not confined to stage2: the AOT smoke
gate `scripts/check/check-aot-smoke.shs` FAILed with its own diagnostic excerpt
empty, because it greps `-i error` from the build log while the real line
(`error: semantic: undefined field 'kind': ...`) sits below the
`!!!!!! END NATIVE-BUILD TRUNCATED STDERR !!!!!!` banner. A `native-build`
failure whose error text is truncated or buffered away is the same class of
problem as the empty stage2 log, and any fix should cover both paths. See
`doc/08_tracking/bug/aot_llvm_void_type_struct_probe_2026-08-10.md`.
