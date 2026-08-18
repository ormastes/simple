# Startup Perf-Budget Lane

Guards `bin/simple` startup latency across the six Phase-D lanes
(plan: `doc/03_plan/compiler/startup_performance/startup_perf_plan_2026-08-17.md`),
each p50 of N=7 samples against committed budgets in `budgets.sdn`:

| lane | command | budget key |
|---|---|---|
| version | `bin/simple --version` | `version_ms` |
| help | `bin/simple build` (prints HELP, exits) | `help_ms` |
| run-hello-warm | `bin/simple run hello_fixture.spl`, same path each sample | `run_hello_ms` |
| run-hello-cold | same, fixture copied to a fresh path per sample | `run_hello_cold_ms` |
| smf-load | `bin/simple hello.smf` (compiled once per run, then timed) | `smf_load_ms` |
| compile-body | `bin/simple compile` with a different function body per sample | `compile_hello_ms` |

Each real run writes an **immutable per-run manifest** to
`build/perf/startup/startup_manifest_<utc>_<pid>.sdn` (unique name, chmod a-w):
binary path/identity/sha256/size+mtime, host, loadavg, sample count, per-lane
p50 AND p95 (N=7 ⇒ p95 = max sample), run-hello max RSS, and opens/mmap counts
via strace when available (`unavailable` otherwise — never fabricated).

Run:

```bash
sh scripts/check/check-startup-perf-budget.shs            # fatal selftest, then measure
sh scripts/check/check-startup-perf-budget.shs --selftest # fixtures only
```

Verdict (last stdout line, detector standard —
`doc/07_guide/infra/detector/detector_standard.md`):

- `PASS — 6 lane(s) measured (N=7, binary=<seed|self-hosted> <path>): <per-lane p50/p95>` exit 0
- `SKIP — bin/simple missing/unresolvable ...` exit 0 (explicit, never a measurement)
- `FAIL — ... <lane> p50=<measured>ms > budget <n>ms` exit 1
- `ERROR — nothing was checked ...` exit 2 (missing budgets file OR missing lane
  key, failed runs, failed selftest)

The verdict records binary identity (rust-seed vs self-hosted) because the two
have very different startup profiles — never compare timings across identities.

Specs: `startup_perf_budget_spec.spl` (verdict/fail-closed contract) and
`startup_perf_lanes_spec.spl` (all-lanes + manifest reproducing spec, plus the
defect-class positive control via the detector's selftest fixtures). Neither
re-times anything — the script is the single timing oracle.

## Updating budgets (the ONLY recorded escape)

Edit `budgets.sdn` and change the value **with a dated comment** explaining the
new measurement and why. There is deliberately no env var or flag override —
a silent override is exactly the escape the detector standard forbids. Budgets
are set well above measured noise (>= p50 x3 and >= p95 x2 on a shared box) so
box load does not flap the lane; see the dated comments in `budgets.sdn`.

Status: ADVISORY (FP rate not yet adjudicated on a named sample; see FP-RATE
line in the script header before any promotion to blocking).
