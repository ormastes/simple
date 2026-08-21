# A7 hardening perf baseline — whole-process wall + max RSS (2026-08-21)

Lane A7 of `doc/03_plan/compiler/hardening/critical_hardening_plan_2026-08-21.md`
(design `doc/01_research/compiler/hardening/simple_hardening_plan_2026-08-21.md`
§18/§19). Purpose: a reproducible process-level baseline so the Any-removal,
mono, closed-match and transition-table lanes can prove they did not regress
startup, compile cost or peak memory. Complements the in-process ns/op
micro-benches in `doc/10_metrics/compiler_hardening/baseline_2026-08-21.md`
(`check-hardening-perf-budget.shs`).

- Guard: `sh scripts/check/check-hardening-perf-baseline.shs` (`--selftest`, `--record`)
- Baseline file: `doc/10_metrics/hardening/perf_baseline.sdn`
- Fixtures: `test/05_perf/compiler_hardening/wall_{hello,enum_match,generic,anybox}.spl`
- Method: `nice -n 10 /usr/bin/time -v`, N=3 per bench, MEDIAN wall and MEDIAN max RSS; one bench process at a time.
- Budget: +100% tolerance on both axes, plus a 0.25s absolute wall floor.

## Binary identity and load (record time)
```
bin/release/x86_64-unknown-linux-gnu/simple  59867576 bytes  2026-08-21 05:10:21 +0000
(Rust seed — prints the "bootstrap seed only" banner; no full-CLI self-hosted binary deployed)
loadavg at record: 37.07 34.23 29.77 -> 37.51 34.42 29.88   (32 cpus, shared box)
recorded: 2026-08-21T05:56:24Z
```

## Measured (median of 3)
| bench | command | lines | wall s | max RSS kB |
|---|---|---|---|---|
| compile_hello | `simple compile -o OUT wall_hello.spl` | 5 | 0.10 | 38796 |
| run_hello | `simple run wall_hello.spl` | 5 | 0.07 | 39340 |
| run_enum_match | `simple run wall_enum_match.spl` (40 variants x 3 match sites, 200k iters) | 225 | 0.85 | 50664 |
| run_generic | `simple run wall_generic.spl` (3 generic fns x 3 types, 300k iters) | 27 | 1.60 | 150476 |
| run_anybox | `simple run wall_anybox.spl` (Any box/unbox, 300k iters) | 18 | 0.33 | 50616 |

Verification run immediately after recording (load 37.5 -> 38.8):
`PASS — 5 bench(es) checked, 0 over budget (+100% tolerance)`. Spread seen in
that second run: run_anybox 0.33 -> 0.64s (1.9x) with everything else within
10% — which is why the tolerance is 2x and the comparison is a median, not a
single sample.

## Caveats
- **Load.** Every number above was taken at load average 34-39 on a 32-cpu box
  shared with 20+ other `simple` processes. Treat them as an upper envelope;
  an idle box will be faster and a baseline re-recorded idle will be TIGHTER,
  so re-record (`--record`, reviewed) rather than compare across load regimes
  when the box quiets down.
- **Binary.** Numbers are for the Rust seed. When a self-hosted full-CLI binary
  is deployed, the baseline must be re-recorded; the header in
  `perf_baseline.sdn` carries the identity so a mismatch is visible.
- **run_generic is timing a miscompile.** On this seed every generic call
  returning a scalar `T` yields `value << 3` (untagged payload) — see
  `doc/08_tracking/bug/generic_struct_field_untagged_payload_seed_2026-08-21.md`.
  The wall/RSS baseline is still valid for regression detection (the guard does
  not check program output), but its 150 MB RSS / 1.6s must not be read as
  "generic cost" until that bug is fixed; expect the number to move when it is.
- Generic RSS is ~3x the other benches (150 MB vs 50 MB): that is the first
  concrete target for the mono lane (§18.4) to improve, and this gate is what
  will show it.
