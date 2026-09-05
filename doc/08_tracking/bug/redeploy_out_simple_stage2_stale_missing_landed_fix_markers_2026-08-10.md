# `build/redeploy_out/simple_stage2` is stale — missing markers for two already-landed fixes

Status: OPEN
Filed: 2026-08-10
Filed by: gate-oracle work on `scripts/check/check-compiler-provenance.shs`

## Finding

`scripts/check/check-compiler-provenance.shs` was given a real fail-closed
verdict (previously exit-code-only / diagnostic-report-only, never asserted
anything). The new oracle asserts: any binary carrying Simple-compiled code
(`simple_syms > 0`, i.e. HYBRID or pure-Simple lineage) must contain every
marker string for a real, already-landed commit in the `MARKERS` table.

Run against the default binary set (`sh scripts/check/check-compiler-provenance.shs`,
which includes `build/redeploy_out/simple_stage2`), the gate is RED:

```
FAIL — 3/6 marker check(s) failed across 2 Simple-symbol-bearing binary(ies):
  .../build/redeploy_out/simple_stage2: marker for 5c75a1bbce0 is ABSENT despite simple_syms=3824 (expected present -- stale build or regression)
  .../build/redeploy_out/simple_stage2: marker for 5c75a1bbce0 is ABSENT despite simple_syms=3824 (expected present -- stale build or regression)
  .../build/redeploy_out/simple_stage2: marker for ab773bb5d5e is ABSENT despite simple_syms=3824 (expected present -- stale build or regression)
```

`bin/release/x86_64-unknown-linux-gnu/simple` (built 2026-08-10) passes the
same check with all 3 real-commit markers present. `build/redeploy_out/simple_stage2`
is dated `Jul 28 00:11` (`stat` mtime), predating both marker commits
(`5c75a1bbce0`, `ab773bb5d5e`), confirming it is a stale build artifact left
in the tree from an earlier redeploy run.

## Why this is left RED, not silenced

Per repo policy, a gate that is catching a real, currently-true defect must
not be weakened to force green. `build/redeploy_out/simple_stage2` genuinely
lacks the fixes the marker table asserts should be present in any
Simple-symbol-bearing binary. Options for a fix (not applied here, out of
scope for the gate-oracle task that found this):

1. Rebuild/redeploy `build/redeploy_out/simple_stage2` from current source so
   it actually carries the landed fixes, or
2. If that artifact is deliberately pinned to an older revision for some
   other lane's purposes, remove it from `check-compiler-provenance.shs`'s
   default `BINS` list (with a comment explaining why it is intentionally
   excluded from the "should have every landed fix" assertion), or
3. Delete the stale artifact if it is not load-bearing for anything.

## Reproduction

```sh
sh scripts/check/check-compiler-provenance.shs   # default binary set, includes the stale artifact -> FAIL
sh scripts/check/check-compiler-provenance.shs bin/release/x86_64-unknown-linux-gnu/simple   # PASS on its own
```
