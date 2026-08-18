# Startup Perf-Budget Lane

Guards `bin/simple` startup latency: p50 of N=7 runs of `bin/simple --version`
and `bin/simple run test/05_perf/startup/hello_fixture.spl`, compared against
committed budgets in `budgets.sdn`.

Run:

```bash
sh scripts/check/check-startup-perf-budget.shs            # fatal selftest, then measure
sh scripts/check/check-startup-perf-budget.shs --selftest # fixtures only
```

Verdict (last stdout line, detector standard —
`doc/07_guide/infra/detector/detector_standard.md`):

- `PASS — 2 command(s) measured (N=7, binary=<seed|self-hosted> <path>): ...` exit 0
- `SKIP — bin/simple missing/unresolvable ...` exit 0 (explicit, never a measurement)
- `FAIL — ... <which> p50=<measured>ms > budget <n>ms` exit 1
- `ERROR — nothing was checked ...` exit 2 (missing budgets file, failed runs, failed selftest)

The verdict records binary identity (rust-seed vs self-hosted) because the two
have very different startup profiles — never compare timings across identities.

## Updating budgets (the ONLY recorded escape)

Edit `budgets.sdn` and change the value **with a dated comment** explaining the
new measurement and why. There is deliberately no env var or flag override —
a silent override is exactly the escape the detector standard forbids. Budgets
are set at measured p50 x3 so shared-box noise does not flap the lane
(2026-08-18 baseline: version 122ms, run-hello 133ms, seed binary).

Status: ADVISORY (FP rate not yet adjudicated on a named sample; see FP-RATE
line in the script header before any promotion to blocking).
