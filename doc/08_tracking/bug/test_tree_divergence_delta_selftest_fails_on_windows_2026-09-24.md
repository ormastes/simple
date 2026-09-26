# check-test-tree-divergence-delta.shs: selftest fails on a Windows/MSYS host, so the scoped-delta escape is unavailable there

Filed: 2026-09-24
Host: DESKTOP-5A4V03J (Windows 11, Git Bash / MSYS2, x86_64-pc-windows-gnu)

## Symptom

```
$ sh scripts/check/check-test-tree-divergence-delta.shs origin/main HEAD
check-test-tree-divergence-delta: ERROR: selftest failed (exit 2):
    check-test-tree-divergence-delta: ERROR — nothing was checked
check-test-tree-divergence-delta: ERROR — nothing was checked
```

The helper's own fatal `--selftest` fails before it scans anything, so it can
never return a verdict on this host. Exit 2 with `ERROR — nothing was checked`
is the correct fail-closed behaviour; the defect is that the selftest itself
cannot pass here, not that it refused.

## Why it matters

`.claude/rules/vcs.md` makes this helper the ONLY sanctioned escape for landing
a change while `check-test-tree-divergence.shs` is red from a pre-existing
divergence backlog. `origin/main` is currently red (3800 diverged vs 965
baselined), so on a Windows host every landing is blocked by a red that the
range did not cause, with the designated escape hatch unusable.

## Equivalent evidence used instead (this range only)

Not a substitute for fixing the helper, recorded so the step-over is auditable:

- `check-test-tree-divergence.shs --ref origin/main` and `--ref HEAD` both
  report the identical verdict:
  `FAIL — 3800 diverged vs 965 baselined (2967 new, 132 fixed-but-still-baselined);
  35 mirror-only (34 unallowlisted, 0 stale-allowlist)`.
- Their full outputs (3147 lines each) were diffed. The ONLY differences are
  two lines naming the run's random temp directory
  (`/tmp/test_tree_divergence_src.XXXXXX`). Every offender entry is identical,
  i.e. the range introduces zero new divergence and fixes none.
- `git diff --name-only origin/main..HEAD -- test/01_unit test/unit
  test/02_integration test/integration` is EMPTY: the range touches no
  test-tree file on either side of any mirror pair.

## Not yet investigated

Which of the helper's fixtures fails, and why, on MSYS. The selftest builds
fixture repositories and runs the guard under job control, signalling the
process group on SIGTERM; both process-group handling and `mktemp`/temp-path
semantics differ on MSYS and are the first places to look. No fix is attempted
here because that belongs with the gate's owner, and a wrong "fix" to a
fail-closed gate is worse than a known-broken one.
