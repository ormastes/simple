# Stage 2 admission source-quiescence invariant is unsatisfiable in the shared working tree

- Date: 2026-08-31
- Severity: high (blocks every bootstrap redeploy attempted from the shared tree)
- Status: OPEN (procedure workaround: bootstrap from a clean detached worktree)

## Symptom

`sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2`
(the trust-root Stage 2 refresh) builds a fully green Stage 2 binary and then
refuses admission:

```
Stage 2: proving struct receiver/runtime capability
error: refused incomplete Stage 2 admission provenance   (stage2_status=4)
```

while `stage2-native-build.log` ends `Build complete: 745 compiled, 0 cached,
0 failed` (129,695 KB binary, 583.3s compile + 79.1s link) and BOTH probes
passed: `stage2-sanity.env: status=pass`, `stage2-receiver.env: status=pass`.
The rejected binary self-reported `simple-bootstrap 1.0.0-RC` (rc=0, no seed
banner).

## Root cause

`bootstrap-from-scratch.sh:2296-2300` fail-closed compares the full source
snapshot taken before the build (`source-inputs-before.txt`) against one taken
after (`source-inputs-after.txt`) and refuses on ANY difference. This tree is
shared by parallel agent sessions that edit `src/**` continuously. During the
~11-minute Stage 2 build window, another lane changed:

- `src/app/spipe/fusion/adjustments.spl` (hash 5753...9d33 -> 9f3d...48a2)
- `src/app/spipe/fusion/graph_source.spl` (added)
- `src/app/spipe_knowledge_provider/main.spl` (changed)

Tool authority was byte-identical (`cmp` clean); the diff is purely concurrent
source edits. The invariant is correct as a security property but cannot be
satisfied where the build window (minutes even warm) overlaps ongoing edits —
retries only re-roll the dice.

## Related blockers hit on the same path (same session)

1. Silent exit 1 from a symlink-aliased logical PWD — see
   `doc/08_tracking/bug/bootstrap_facade_check_silent_exit_on_symlinked_pwd_2026-08-31.md`.
2. `error: could not bind Stage 3 git HEAD/dirty state`:
   `bootstrap_stage3_git_state` (scripts/check/lib/bootstrap-stage3/authority.shs:1425)
   exits 1, with no path named, on any untracked entry that is neither regular
   file nor symlink. Two stale artifacts left by other sessions triggered it:
   `bootstrap/.input-snapshot` (self-referential symlink farm, ELOOP) and
   `hal-batch2/` (nested git repo, listed as `hal-batch2/` by
   `git ls-files --others`). Both archived to
   `/mnt/data/tmp/archived-input-snapshot/`. The helper should name the
   offending path in a typed error line.

## Recommended procedure (and suggested doc fix)

Run bootstraps from a clean detached worktree of a named commit:
`git worktree add --detach <tmpdir> <sha>` and run
`scripts/bootstrap/bootstrap-from-scratch.sh` there. Same source, no seed
copying, no receipt forgery; the quiescence invariant holds by construction
and the run is reproducible against a commit id. `.claude/rules/bootstrap.md`
should document this as the standard bootstrap procedure on shared hosts.
