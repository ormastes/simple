# `native-build` worker times out, making a mandatory pre-push guard permanently RED

**Filed** 2026-08-17. **Status** OPEN. **Impact** blocks EVERY guarded push on
this host, for every lane.

## Symptom

`sh scripts/check/check-native-extern-fabrication.shs` fails immediately with:

```
FAIL — control fixture (no extern) no longer builds under native-build
```

It is wired into `pre-push-conflict-tree-guard.shs`, so `git push` is blocked
for all lanes with:

```
pre-push: BLOCKED by check-native-extern-fabrication.shs (status 1) for range
          native-build extern-fabrication probe (full scan, not range-bound)
```

## Root cause — NOT extern fabrication

The guard discards the compiler's actual error, so the verdict is misleading.
Reproduced directly with the guard's own arguments:

```
env -u SIMPLE_BOOTSTRAP bin/simple native-build --source test/fixtures \
  --entry-closure --entry test/fixtures/native_extern_fabrication_probe/control.spl -o /tmp/ctrl.bin
CTRL_RC=255
error: native-build worker timed out after 7200s before producing a binary.
  The interpreted worker loads the whole compiler + LLVM import graph before any
  codegen; a large --source set (e.g. src/os + src/lib) exceeds the budget.
  Raise --timeout, shrink --source, or use the in-process backend for
  cross-target builds.
```

So `native-build` cannot complete at all here. The guard is behaving correctly —
its header states the control fixture exists precisely so the gate "cannot be
vacuously green because native-build itself is broken". It is reporting real
infrastructure breakage, not a fabrication finding. **Do not "fix" this by
deleting or relaxing the control.**

## Why the verdict line is still a defect

`check-native-extern-fabrication.shs:71-75` runs the control build inside an
`if !`, discards its log, and prints only "no longer builds". The 255 and the
timeout text are captured to `$ctrl_log` but never surfaced on failure, so the
operator sees a fabrication-shaped verdict for a timeout. Suggested minimal
fix: echo the last few lines of `$ctrl_log` on that failure path, the way the
`[default]`/`[strict]` branches already do for their own logs.

## Scope note

This is host/toolchain territory, not a product-code defect in any one lane. It
was found by the unstable_test_mode lane while trying to land two files (a
check script and a tracking doc) that cannot possibly affect `native-build`.
Handing it off rather than working around it: the correct resolutions are to
raise the worker timeout, shrink the guard's `--source` set, or use the
in-process backend as the error text itself suggests — all decisions for
whoever owns the native-build lane.

**Never** resolve this with `git push --no-verify`. Nine mandatory guards exist
because two unbuildable trees reached `main` on 2026-08-11 exactly that way.

## Related

- `doc/08_tracking/bug/origin_main_unbuildable_rust_seed_2026-08-11.md`
- Guard-integrity note: these native-build guards read `src/` from the
  *invoking* tree, so the same commits can pass from one checkout and fail from
  another. Confirmed here that the FAIL reproduces from BOTH the main tree and a
  clean `git worktree` at the origin tip, so this one is not worktree-specific.
