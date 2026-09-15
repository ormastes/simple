# Pinned Stage-2 candidate SIGSEGVs at the monomorphize phase

- Status: OPEN (2026-09-13)
- Found: bootstrap lane BOOT-11, `work/bootstrap-codegen-1-2026-09-13`
- Severity: the pinned candidate cannot compile anything, so it cannot be used
  as the reference compiler for a native-codegen RED/GREEN measurement.

## Binary

`/home/yoon/dev/simple-boot9/build/bootstrap-boot9b/stage2-rejected/aarch64-unknown-linux-gnu/simple`
(read-only copy taken 2026-09-13), size 152198272, sha256 prefix `99ba0cf430d255a4`.
`--version` answers cleanly: `simple-bootstrap 1.0.1-beta.1`.

Note for whoever reads BOOT-11's guide: the path given there
(`build/bootstrap-boot9b/stage2/aarch64-unknown-linux-gnu/simple`) is empty on
disk; the artifact is under `stage2-rejected/`.

## Verdict

```
[build] phase=monomorphize state=running unit_kind=modules ... task_done=4 task_total=6 elapsed_ms=4897
timeout: the monitored command dumped core
Segmentation fault           (rc=139)
```

Reached with the redeploy-gate's own invocation shape
(`--backend llvm --runtime-bundle core-c-bootstrap --entry-closure --mode one-binary`,
`SIMPLE_BIN`/`SIMPLE_BOOTSTRAP_DRIVER`/`SIMPLE_FRONTEND_DELEGATE` all set to the
candidate, `SIMPLE_LIB=<worktree>/src`) on a three-module fixture. It needs
`SIMPLE_PACKAGE_INDEX_COLD_INIT=1` first, else it exits 1 with
`persistent package index admission failed: scv-authority-missing`; with that
set it reaches monomorphize and dies there.

This is consistent with, and adds a phase to, the standing record that every
tracked stage binary crashes (`.claude/rules/vcs.md`, the
`check-stage-binaries-runnable.shs` advisory guard, measured 2026-08-18).
