# Stage 2 admission source-quiescence invariant is unsatisfiable in the shared working tree
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Fix implemented 2026-11-09 — verification pending

Owner decision 2026-11-09: scope the before/after source snapshot to
build-input paths only. `bootstrap_stage3_source_snapshot_once`
(`scripts/check/lib/bootstrap-stage3/command-snapshot.shs`) now prunes every
top-level `src/app/<dir>` NOT named in the checked-in
`scripts/bootstrap/stage2-build-input-app-dirs.txt`. All other authority roots
(`src/compiler`, `src/lib`, `src/os`, `src/runtime`, ..., `scripts/bootstrap`,
`scripts/check/lib`) and top-level `src/app` files stay fully hashed. The list
is mandatory and non-empty (fail closed), and editing it is itself snapshot
churn because it lives under `scripts/bootstrap`.

The list is the transitive closure of `use|from|import app.X` reachable from
the core roots, verified by `sh scripts/bootstrap/stage2-build-input-app-dirs-check.shs`
(`--selftest`, `--print` to regenerate; FAIL names any unlisted closure dir).
Of the incident's three paths, `src/app/spipe/**` is now out of scope;
`src/app/spipe_knowledge_provider` IS a real build input (imported from the
closure) and correctly still refuses.

Evidence: `test/02_integration/bootstrap_stage3_source_snapshot_scope_test.shs`
— green with the fix; red (`FAIL: unlisted app dir present in snapshot`) with
`command-snapshot.shs` reverted. Verification pending a real Stage 2 run in the
shared tree.

## Review round 2026-11-09 (owner-decision follow-ups)

1. Wiring: `stage2-build-input-app-dirs-check.shs` is now a must_check_gates.sdn
   row (`local-stage2-build-input-app-dirs`, fast-gates tier), so the closure
   check runs in CI instead of only by hand.
2. Coverage: the closure walker now also scans TOP-LEVEL src/app files
   (src/app/*.spl, src/app/*.sdn) — entry points such as src/app/main.spl reach
   app dirs no importing module names. Path-spelled reach (`src/app/<dir>`
   under scripts/bootstrap, scripts/check/lib) is reported as NOTEs, not
   verdict failures: those references live in phase-4 tooling, sanity runners
   and fixtures that execute AFTER stage2/3 admission, and listing them would
   re-break this fix. Import channels stay fail-closed. Selftest: 4 fixtures.
   Also regenerated the list: `t32_cli` is import-reachable via
   src/app/cli/_CliMain/main_and_help.spl and is now listed.
3. Red/green: with command-snapshot.shs reverted to the release/1.0.0 base,
   bootstrap_stage3_source_snapshot_scope_test.shs FAILs ("unlisted app dir
   present in snapshot"); with the fix it prints
   bootstrap_stage3_source_snapshot_scope=true. Captured on 2026-11-09.
