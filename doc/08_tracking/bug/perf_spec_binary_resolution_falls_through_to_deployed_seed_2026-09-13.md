# A perf spec's binary resolution falls through to the deployed seed in directory mode
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

- Status: OPEN (2026-09-13)
- Found by: PERF-6 while diffing `test/05_perf/interp/` between two seeds

## What

`test/05_perf/interp/while_loop_shape_parity_spec.spl` (and PERF-6's new
`block_scope_shadow_parity_spec.spl`, copied from it) resolve the binary under
test with `simple_binary()`: `SIMPLE_PERF_SELF_BIN` if it is executable, else a
fallback chain ending in `bin/simple`.

**The test runner DROPS `SIMPLE_PERF_SELF_BIN` in DIRECTORY mode and propagates
it in single-file mode.** Measured with an env-probe spec run both ways on the
same binary:

```
simple test <file>  -> SIMPLE_PERF_SELF_BIN=/probe/XYZ
simple test <dir>   -> (variable ABSENT in the child)
```

In a fresh worktree the first four fallback candidates do not exist
(`src/compiler_rust/target/release/simple`, the three `bin/release/<triple>/`
paths), so the chain lands on `bin/simple` -- which a lane hand-links to the
DEPLOYED seed, and the deployed seed can predate the very change under test.

## The measurement that identified it

PERF-6's suite diff showed `while_loop_shape_parity_spec.spl` reporting
`shape_slow_right` at **6,835,637 us** with the `interp-perf-counters:` header
present and the `WHILE_INLINE_INT_ITERS` row ABSENT. Three binaries, same
fixture, run directly:

| binary | elapsed_us | header | WHILE_INLINE_INT_ITERS row |
|---|---:|---|---|
| deployed seed, Sep 6 (`bin/simple`) | 8,627,802 | present | **absent** |
| `simple.base` (origin/main f26970e9d93) | 27,657 | present | 2,000,000 |
| `simple.v1` (PERF-6 candidate) | 29,071 | present | 2,000,000 |

The anomalous child matches the deployed seed 3 for 3 and either pinned seed 0
for 3. The Sep-6 seed predates PERF-3's generalised matcher, so it has neither
the matcher nor the counter, which is exactly what the child reported.

## Consequence

A spec that silently measures a different binary than the lane intended is worse
than one that fails: the 0/7 it produces reads as "this seed is broken" when it
actually means "the gate correctly refused a binary that has no such counter".
PERF-6 spent an hour on interleaved runs before the fingerprint was run down.

## Fix shape

1. **Print the resolved binary before asserting.** PERF-6 added
   `print "[perf] binary={binary}"` to every scenario of
   `block_scope_shadow_parity_spec.spl`; `while_loop_shape_parity_spec.spl`
   should get the same line. One line, and the trap is visible in the first log
   line instead of an hour later.
2. The runner's directory mode should propagate `SIMPLE_PERF_SELF_BIN`, or the
   specs should read `SIMPLE_TEST_BINARY` (which the runner DOES export in both
   modes, pointing at the binary actually running the suite) before falling
   through to `bin/simple`.

Not fixed here: (2) touches the runner and the sibling spec, both outside
PERF-6's scope, and (1) is applied only to the spec this lane owns.

## Addendum 2026-11-11 — lane runner5: SUPERSEDED (fix verified on refreshed seed)

Fix shape 2 (the actual defect) has been implemented: the test runner now
forwards `SIMPLE_PERF_SELF_BIN`. `src/app/test_runner_new/test_runner_client.spl`
`_binary_override_vars()` (~line 708) includes `"SIMPLE_PERF_SELF_BIN"`, so any
allowlisted binary selector set in the invoking environment makes the client
bypass the session daemon and propagate the variable to the spec child. The
mechanism is pinned by `scripts/check/check-perf-regression-tests.shs:877-886`
(greps for `"SIMPLE_PERF_SELF_BIN"]` in the client). Ledger row
`doc/08_tracking/bug/bug_db.sdn:5820` (2026-11-09) records
"fix-implemented-verification-pending … Not re-run" — this addendum supplies
the pending verification.

Seed-smoke verification on refreshed seed (build-commit 0791c2b7f4a7):
re-ran the bug's own measurement matrix with an env-probe spec
(`build/review/p3fix-runner5-20261111/perf_bin_probe/perf_bin_probe_spec.spl`,
gitignored temp):

    SIMPLE_PERF_SELF_BIN=PROBE_XYZ_VALUE bin/simple.exe test <file>  -> OK (child sees the var)
    SIMPLE_PERF_SELF_BIN=PROBE_XYZ_VALUE bin/simple.exe test <dir>   -> OK (child sees the var)

Both single-file and DIRECTORY mode now deliver `SIMPLE_PERF_SELF_BIN` to the
child — the 2026-09-13 "directory mode drops the variable" behaviour no longer
reproduces.

Residual (non-blocking) gap from the original "Fix shape": the sibling
`while_loop_shape_parity_spec.spl` still does not print the resolved binary
(fix shape 1 was applied only to `block_scope_shadow_parity_spec.spl`, the
spec PERF-6 owned). The silent-wrong-binary defect itself is closed by the
runner forwarding; the print line remains a diagnostic nice-to-have.

Verdict: SUPERSEDED — runner fix in test_runner_client.spl, verified on the
refreshed seed in both runner modes.

