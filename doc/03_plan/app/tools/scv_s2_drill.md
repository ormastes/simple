# SCV S1 -> S2 Drill (SCV-MIG-14)

## What the drill proves
The S2 gate means: SCV owns implicit snapshots, and the whole `.scv` store can
be deleted without losing anything — the sidecar (colocated git) plus a
re-snapshot fully reconstruct SCV state. Losing SCV must be cheap.

The drill (`scripts/scv-migration/steps/SCV-MIG-14.shs`) runs in a temp dir,
never against this repo:

1. Create a temp colocated git repo (2 files, 1 commit).
2. `scv init` + `scv snapshot` + `scv checkpoint`.
3. `rm -rf .scv` — simulate total SCV loss.
4. `scv init` + `scv snapshot` again.
5. Assert, per the month-plan MIG-14 row folded with the S2 recovery drill:
   - `scv doctor` PASS
   - `scv fsck` PASS
   - `scv db-index` rebuild succeeds
   - `scv verify-backends --git .` PASS (byte-for-byte vs git HEAD)
   - `git fsck --strict` clean (the sidecar was never harmed)

Note: the plan row says "on a copy of this repo"; the drill deliberately uses a
temp repo — a full copy of this tree is not viable on the shared host, and the
gate property (delete + recover + verify) is repo-size independent.

## How to run
```sh
sh scripts/scv-migration/steps/SCV-MIG-14.shs
```
Verdict is the last stdout line: `PASS` exit 0 / `FAIL` exit 1 /
`ERROR — nothing was checked` exit 2 (setup problems, never a pass).

## What a failure means
- `doctor`/`fsck`/`db-index` failing after re-init: re-snapshot does not
  reconstruct consistent SCV state — S2 is NOT met; stay at S1.
- `verify-backends` FAIL: recovered SCV tree diverges from git bytes — the
  sidecar mapping is lossy; stay at S1 and file the mismatch rows.
- `git fsck` failing: the drill (or SCV) mutated the git backend — a read-only
  contract violation; treat as a P0 bug.
