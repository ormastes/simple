# Bootstrap stage2: silent exit-1 with a 0-byte stage2-native-build.log

- **Date:** 2026-08-17
- **Status:** PARTIALLY FIXED 2026-08-17 (diagnosis path landed for real - the earlier MITIGATED claim was false, see the correction below); root output-buffering defect still open
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

## 2026-08-17 correction — the claimed mitigation was NEVER landed

The "Fix (additive...)" section above describes a diagnostic block in
`bootstrap-from-scratch.sh`. **It does not exist and never did.** None of the
strings it describes are in the file, and
`git log -S 'precondition refusal' --all -- scripts/bootstrap/bootstrap-from-scratch.sh`
returns nothing — so this was not a shared-tree clobber, it was never committed.
The doc's `Status: MITIGATED` was wrong for the whole time it stood.

Landed now, as a standalone testable guard rather than inline script text:

- `scripts/check/check-stage-log-diagnosable.shs` — classifies a stage failure
  into log-never-created (wrapper precondition refusal, pre-exec) /
  log-exists-0-bytes (compiler died unflushed) / content-with-no-diagnostic-line
  (the `[bootstrap-error-count] count=21` shape) / exit-125 (wrapper post-run
  verification, NOT a compile failure) / diagnosable-with-text. Verdict is the
  last stdout line, `PASS`/`FAIL` exit 1/`ERROR` exit 2; a run that checked zero
  things is ERROR, never a vacuous pass. Wired into stage2's failure path in
  `bootstrap-from-scratch.sh`, which additionally prints an explicit
  "stage2 failed with NO diagnostic text ... this is itself a defect" line.
- `--selftest` is fatal, 10 fixtures, including the two that must PASS and the
  below-the-truncation-banner case the AOT smoke gate misses:
  `PASS — 10 selftest fixture(s), 0 failed`.

The selftest earned its keep on first run: the counts-without-text fixture
caught a real bug in the guard where `grep -c ... || echo 0` produced the
two-line value `"0\n0"`, so the numeric test errored instead of comparing and
an UNDIAGNOSABLE log was classified as diagnosable — a fail-open guard.

## The deeper half: counts without text (fixed)

`src/compiler/80.driver/driver_hir_pipeline_lowering.spl` emitted
`[bootstrap-error-count]` unconditionally while the diagnostic TEXT was gated
behind `SIMPLE_BOOTSTRAP_DEBUG=1` and additionally capped at `source_idx < 20`.
The end-of-phase `[collect-all]` report does print the text — but only if the
process survives to reach it, which a stage dying at exit 139 does not. That is
why six stage-3 failures produced counts and no message.

Fatal diagnostics now print at the moment they are recorded. Demonstrated on a
real failing build (`rc=1`, read into a variable, not through a pipe):

```
[bootstrap-error-count] source_idx=0 point=post-lowering count=0
[hir-fatal] source_idx=0 path=.../user.spl error_idx=0 text=HIR lowering error in .../user.spl: unresolved type: WireWriteV1
[hir-fatal-count] source_idx=0 path=.../user.spl count=1 shown=1
[bootstrap-error-count] source_idx=0 point=post-diagnostics count=1
[hir-poisoned] source_idx=0 path=.../user.spl module=... errors=0->1
```

and the guard reads that log as `PASS — 1 check(s), stage demo failed (exit 1)
and said why`, versus `FAIL — ... with NO diagnostic text` on a 0-byte log.

Still open: `native-build` output buffering itself. The guard names the case and
refuses to be silent about it, but does not make a mid-build death flush.

## Lane J re-verification 2026-08-17 (classified by CONTENT, not SHA ancestry)

**Verdict: PARTIALLY-FIXED, root defect STILL-OPEN.** Content confirms the diagnosis path is
present: `scripts/bootstrap/bootstrap-from-scratch.sh:1963` captures `stage2_status=$?` on
the line AFTER the build (not through a pipe), and :1973 unconditionally announces
`stage2-native-build log: ${log_dir}/stage2-native-build.log`, with the sanity gate at
1974-1985 able to force `stage2_status=2`. The underlying 0-byte-log output-buffering defect
is not addressed by that code and remains open.
Related fix landed this session in the SAME file — see
`bootstrap_stage2_capability_log_phantom_2026-08-17.md`.
