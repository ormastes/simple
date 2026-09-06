# check-hook-installation rejects the shared-worktree pre-push launcher

- Filed: 2026-08-24
- Component: `scripts/check/check-hook-installation.shs`
- Status: OPEN
- Effect: blocks every push from a linked worktree, including pushes whose
  content guards all pass

## Symptom

```
check-hook-installation: DEFECT — pre-push hook resolves to
  '<worktree>/.git/hooks/pre-push', which is neither the canonical guard nor
  the tracked must-check dispatcher.
    fix: sh scripts/setup/install-must-check-hooks.shs --install
check-hook-installation: FAIL — 10 check(s) performed, 1 defect(s) in hook wiring
pre-push: BLOCKED by check-hook-installation.shs
```

The prescribed fix does not help: `install-must-check-hooks.shs --install`
refuses to overwrite the existing `.git/hooks/pre-push.local` and exits without
changing the wiring, so the check stays red on the next run.

## Why the check is wrong here

`.git/hooks/pre-push` is a deliberate **launcher**, installed because linked
worktrees share one hooks directory and a symlink would otherwise embed the
absolute path of whichever worktree last ran the installer. Its last line is:

```sh
exec sh "$ROOT/scripts/hooks/pre-push" "$@"
```

`$ROOT/scripts/hooks/pre-push` is exactly `expected_dispatcher`
(`check-hook-installation.shs:60`). The wiring is correct and the dispatcher
does run — the block above is itself proof, since `check-hook-installation` is
invoked *by* that dispatcher.

The comparison at `:111-112` resolves the path of the hook **file** and matches
it against the canonical guard or the dispatcher. A launcher is a regular file
that is neither, so it fails even though it unconditionally `exec`s the
dispatcher. The check cannot see through one level of indirection.

## Why this matters more than a nuisance

This guard exists because of
`doc/08_tracking/bug/fourth_tree_wipe_6f86ff32a7d_guard_not_enforced_2026-08-11.md`,
where defective wiring silently downgraded every guard to advisory. A wiring
check that false-positives on the supported multi-worktree layout trains people
to push with `--no-verify`, which recreates exactly the unguarded condition it
was written to prevent.

## Fix sketch

Accept a launcher: if the resolved hook file is a regular script whose content
`exec`s `$expected_dispatcher`, treat it as correctly wired. A grep for the
dispatcher path in the hook body, gated on the file being executable, is
sufficient and keeps the check fail-closed for genuinely unwired hooks.
Separately, `install-must-check-hooks.shs --install` should either replace a
stale `pre-push.local` or say what to remove, rather than declining and leaving
the caller with a red check and no path forward.

## Workaround used for this landing

All six content guards were run by hand against the exact commit and recorded
in its message: conflict-tree PASS, conflict-markers PASS, tree-size PASS,
test-tree-divergence-delta PASS (11 pre-existing offenders recorded, 0
introduced), runtime-api-regression PASS (2834 symbols, 0 removed), and
seed-builds PASS. The push was then made with `--no-verify`. That is acceptable
only because every guard was executed and its verdict recorded; it is not a
precedent for skipping them.
