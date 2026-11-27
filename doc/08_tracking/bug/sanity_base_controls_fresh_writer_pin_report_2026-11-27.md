# sanity-base-controls FRESH_WRITER "stale pin" report: does not reproduce

- Date: 2026-11-27
- Status: owner-review (filed, not re-pinned, per the hello-sanity lane brief)
- Area: pre-p2 stage2 sanity trust gate, `scripts/check/lib/bootstrap-stage3/sanity-base-controls.py`

## Report

An earlier lane reported that `scripts/bootstrap/tests/sanity-base-controls-test.py`
fails on Windows because the pinned writer
`FRESH_WRITER = 315ea01f8d725590b9da5ea8d35513ebab3b1852454f147819f5c599adffead8`
is stale. It asked for a bug doc instead of a re-pin.

## Measured (release/1.0.0 at 60ad48d5f3f)

- `sha256(scripts/check/lib/bootstrap-stage3/sanity-control-functions.shs)` =
  `315ea01f8d725590b9da5ea8d35513ebab3b1852454f147819f5c599adffead8`. I got this
  value from the committed blob (`git cat-file -p origin/release/1.0.0:...`) and
  from both Windows checkouts. The pin matches.
- The pin was already repaired by `cf8b3bb10c4` (2026-11-26, "re-pin reviewed
  sanity writer identity after 8fe2ea40"), which replaced `ed4787d0…`. The
  stale-pin report most likely predates that commit.
- `python -B scripts/bootstrap/tests/sanity-base-controls-test.py` on Windows
  with Python 3.13 runs 12 tests: 7 pass, 4 are skipped as POSIX-only, and 1 fails.
  `test_helper_identity_matches_shell_gate` and the writer-identity checks pass.

## Residual failure (different defect)

`test_shell_dispatch_gates` asserts `Git Bash must accompany the Git executable`.
It resolves bash as `which(git).parent.parent / 'bin/bash.exe'`. When the test runs
from Git Bash, `which git` returns `C:/Program Files/Git/mingw64/bin/git.exe`, so
the probe looks for `mingw64/bin/bash.exe`, which does not exist. Run from a shell
whose PATH puts `Git/cmd/git.exe` first, the probe resolves `Git/bin/bash.exe`.
The failure therefore depends on PATH order. It is not a pin problem.

## Owner decision needed

1. Close the stale-pin report as superseded by `cf8b3bb10c4`.
2. Decide whether the Git Bash probe should also accept the `mingw64/bin/git.exe`
   layout (that is, walk up to the Git install root). Any edit to
   `sanity-base-controls-test.py` belongs to the pre-p2 trust-gate owner. It is
   not part of the hello-sanity twin work, so this lane made no edit.
