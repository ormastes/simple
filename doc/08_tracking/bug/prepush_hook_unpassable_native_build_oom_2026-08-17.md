# Pre-push hook is unpassable: check-native-extern-fabrication depends on native-build, which is SIGKILLed at >24 GB

Status: OPEN (P1) — blocks every push to `main`, including releases.

## Symptom

`git push` is refused by `.git/hooks/pre-push`:

```
pre-push: BLOCKED by check-native-extern-fabrication.shs (status 1) for range
          native-build extern-fabrication probe (full scan, not range-bound)
```

Running the guard standalone (`sh scripts/check/check-native-extern-fabrication.shs`,
exit 1) gives three FAIL lines:

```
FAIL — control fixture (no extern) no longer builds under native-build
FAIL — [default] native-build exited 143, but the log never
       failure, not the expected extern-fabrication refusal. Investigate
FAIL — [strict] native-build exited 143, ...
```

## Root cause — not extern fabrication

Exit **143 is SIGTERM**: the RSS monitor killing the native-build worker. The
guard is behaving *correctly* — it refuses to infer the expected
extern-fabrication refusal from a build that died for an unrelated reason, and
says so instead of passing vacuously. It is a victim, not the defect.

The underlying defect is the native-build worker's memory blowup, measured this
session:

- The worker is the entire compiler running **interpreted**
  (`bin/simple run src/app/cli/native_build_worker.spl`).
- RSS climbs monotonically through `parse`: **3.7 → 3.9 GiB in 20 s** on a
  one-module, no-import fixture.
- On a 20-line fixture it was killed by `kill_simple_monitor` at
  **rss=24159MB ≥ 24000MB**, still loading `src/compiler/20.hir/**`, having
  emitted 0 `unresolved name` lines and produced no binary.
- Concurrent workers from other lanes were observed at 15–17 GiB.

Related records:
- `native_build_source_closure_zero_sources_2026-08-17.md` — the allocation
  abort was being **misreported as a 7200 s timeout**; fixed in
  `src/app/cli/native_build_main.spl` so the real cause is now named.
- `native_trailing_default_param_guard_*` — same blocker, same exit 143.
- `stdlib_eprint_shadows_prelude_builtin_program_wide_2026-08-17.md` — fix
  applied but UNVERIFIABLE for this reason.

## Impact

`origin/main` is in a state where its own pre-push hook cannot pass. Any lane
that pushes must either fix native-build's memory use or override the hook.

## Override taken for the 1.0.0-RC release (recorded, not hidden)

The 1.0.0-RC release commit was pushed with `--no-verify`, with explicit user
authorization, after independently validating the tree:

| check | verdict |
|---|---|
| check-no-conflict-tree-push | PASS — 1 commit, 0 conflict trees |
| check-no-conflict-markers-push | PASS — 50 files scanned, 0 markers |
| check-tree-size-push | PASS — base 115562 files, 0 structural faults |
| check-runtime-api-regression-push | PASS — 2795 symbols, 0 removed |
| check-seed-builds-push | PASS — 50 files, compiles cleanly |
| check-c-runtime-compiles-push | PASS — 106 files, 0 errors |
| check-test-tree-divergence-delta | PASS — 71 pre-existing, 0 introduced |
| **check-native-extern-fabrication** | **FAIL — native-build SIGTERM at 24 GB** |

The released diff is provably version-only (0 non-version lines) and
`cargo check --release --bin simple` is clean at that tree, so the override
carries no unvalidated content — the blocked guard could not have assessed it
either way, since native-build never ran.

## Exit criteria

1. The native-build worker builds a 20-line fixture inside a sane RSS budget.
2. `check-native-extern-fabrication.shs` reaches a real PASS or a real
   extern-fabrication FAIL — never exit 143.
3. Pushing `main` no longer needs `--no-verify`.
