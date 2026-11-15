# push-stage2-parent-runtime-inheritance FAILs under parallel push-batch load (Windows)

- Status: open
- Severity: P2
- Found: 2026-11-14, Windows host (Git Bash), worktree `C:/dev/wt/lbs-20261114`
- Script: `scripts/check/check-stage2-parent-runtime-inheritance.shs`

## Observed

In the hook's parallel blocking batch (`check-push-must-pass.shs --from-pre-push-hook`,
12 blocking gates running concurrently) the gate printed:

    FAIL — original runtime and producer stamp not admitted

That is control 1: `bootstrap_stage2_parent_runtime_verify` rejected an untouched
fixture directory right after snapshotting it. The same script PASSed (5 controls)
in two sequential runs (`SIMPLE_PUSH_SEQUENTIAL_GATES=1`) on the same tree, with
nothing changed in between. A fixture that only fails under load means the
snapshot/verify pair depends on something that is not stable between two calls
(timing, a path, or the `/proc` fd branch in
`bootstrap_stage3_directory_snapshot`, `scripts/check/lib/bootstrap-stage3/authority.shs:3533`).

## Not done

Root cause not investigated (out of scope for the push-budget lane). Reproduce by
running the gate 10x concurrently with `SELFTEST_GREEN_MARKER_DIR=none`.
