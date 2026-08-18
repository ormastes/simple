# Dual-run (C/Simple) shadow harness

## What this is

A small helper, `src/lib/common/spec/dual_run.spl`, that lets a spec run a
pure-Simple implementation and its C/Rust `rt_` oracle side by side on the
same input and record whether they agree. It is goal 6 of the
`binary_runtime_hardening` plan's Wave 4: "a framework that runs BOTH the C
and Simple implementations at runtime to check robustness" — the "shadow
mode during migration" step between "flip provider" and "C becomes test
oracle".

## What it proves

For each already-migrated pair listed in
`doc/08_tracking/c_migration/c_migration_inventory.sdn`, the pure-Simple
replacement and its retained C/Rust oracle are run on the *same* inputs
inside one test loop and compared. This catches:

- accidental behavioural drift introduced by later edits to either side,
- sign-of-zero / NaN handling differences (`dual_check_f64`'s `bit_exact`
  flag; NaN vs NaN is treated as agreement, not divergence, since IEEE-754
  NaN != NaN would otherwise flag a matching "not a number" result as a
  false divergence),
- text-formatting drift for the text-returning pairs (`dual_check_text`).

## API surface

`src/lib/common/spec/dual_run.spl`:

- `dual_check_f64(name: text, simple_result: f64, oracle_result: f64, bit_exact: bool) -> DualVerdict`
  — NaN-safe; `bit_exact: true` additionally distinguishes `-0.0` from
  `0.0` via text formatting (plain `==` treats them equal).
- `dual_check_text(name: text, simple_result: text, oracle_result: text) -> DualVerdict`
- `DualVerdict { pair_name, agree, simple_repr, oracle_repr }` — carries
  full repro info so a caller can report a divergence without re-running
  anything.
- `dual_verdict_report(v: DualVerdict) -> text` — one-line human summary.

## Adding a new pair

1. Pick an already-migrated entry from `c_migration_inventory.sdn` whose
   `path` is not one of the contested/in-flux areas (see below).
2. In `test/01_unit/lib/common/spec/dual_run_shadow_spec.spl`, add an `it`
   block: declare the `extern fn rt_...` oracle, call both sides on a
   handful of representative + edge-case inputs, wrap each result pair in
   `dual_check_f64`/`dual_check_text`, and `assert_true(v.agree)`.
3. Run `bin/simple test test/01_unit/lib/common/spec/dual_run_shadow_spec.spl`
   and `sh scripts/check/check-dual-run-shadow.shs`.

Areas to avoid (contested/in-flux at the time this harness was written —
check current state before reusing): `math/special.spl`, `math/cbrt.spl`,
`base_encoding/**`, `gzip/**`, `string_core.spl`, `spec/evidence/**`.

## Gate

`scripts/check/check-dual-run-shadow.shs` runs `--selftest` first (fatal),
then the real spec, and prints a verdict as its last stdout line:
`PASS — <n> pair(s) checked, <m> case(s), 0 divergent` / `FAIL — ...` (exit
1) / `ERROR — nothing was checked` (exit 2).

## Honest limitation

**This runs both implementations only inside test specs.** It proves the
two sides agree on the inputs the spec author chose to exercise, at the
moment the spec runs. It is **not** a production shadow harness that
dual-runs both implementations on live traffic, and it does not catch a
divergence on an input nobody wrote a test case for. A true production
shadow (route real requests to both, compare, alert on drift, keep the
Simple side's result authoritative) is a separate, unbuilt piece of work.
