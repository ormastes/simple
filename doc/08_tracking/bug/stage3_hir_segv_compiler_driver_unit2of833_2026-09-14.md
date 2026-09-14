# Stage 3 native-build SEGVs in the HIR phase at unit 2 of 833 (`compiler.driver.driver*`)

- **Filed:** 2026-09-14
- **Status:** OPEN — blocks every Stage 3 / Stage 4 / deploy on macOS arm64
- **Tree:** `origin/main` `4f4d0e12832` (includes #951, #952, #955, #968)
- **Lane:** F74 round 3, macOS arm64, worktree `agent-affc884d75d16fbde`

## Symptom

`--resume-stage3-from-admitted` dies after ~23 minutes:

```
error: Stage 3 native-build failed (shell=139 worker=absent effective=139
       class=shell-signal-exit signal=signal-number-11 route=direct fallback=none)
```

`stage3-native-build-status.env`: `status=fail shell_exit_status=139
diagnostic_class=shell-signal-exit signal_identity=signal-number-11`.

## Crash point

From `stage3-native-build.log` (preserved at `build/f74logs/stage3-run5-native-build.log`),
lines 11971-12072 — the HIR phase, second unit of 833:

```
[build] phase=hir ... done=1 total=833 ... current=app.cli.bootstrap_main        <- succeeded
[build] phase=hir ... done=1 total=833 remaining=832 ... current=compiler.driver.driver
scripts/check/lib/bootstrap-stage3/command-snapshot.shs: line 274:
  69063 Segmentation fault: 11  env -i "HOME=$bootstrap_stage3_r...
```

The process that dies is the admitted Stage 2 compiler
(`.../stage3/aarch64-apple-darwin/stage2-admitted/simple`), SEGV, no diagnostic
of its own.

## This is forward progress, not a regression

The previous run of this lane (tree `def2a9c30a1`) failed earlier and
differently: 12 HIR lowering errors of the form

```
error: in-process native-build: HIR lowering error in src/app/cli/bootstrap_main.spl:
  imported enum `UnaryOp` has no declaration owner
```

PR #952 fixed exactly that. On `4f4d0e12832` the count of
`has no declaration owner` in the build log is **0**, and
`app.cli.bootstrap_main` now lowers successfully. The chain advanced past that
defect into this one.

## Not diagnosed

No core dump was captured and the crashing unit was not narrowed below
`compiler.driver.driver*`. Two sibling records filed the same day describe
Stage-2-compiler SEGVs in a different shape
(`stage2_native_method_scoped_dict_field_write_segfaults_2026-09-14.md`,
`stage2_native_class_field_text_dict_owner_lost_2026-09-14.md`); whether this is
the same root cause is **unverified**.

## Consequence

No Stage 3 artifact, therefore no Stage 4 and no deploy. `bin/release/` is
untouched; no binary was published and nothing was forged.
