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

## Wired pairs (13, `test/01_unit/lib/common/spec/dual_run_shadow_spec.spl`)

| C-MIG id | Simple function | C/Rust oracle |
|---|---|---|
| C-MIG-0031 | `numeric_round.floor_f64` | `rt_math_floor` |
| C-MIG-0032 | `numeric_round.ceil_f64` | `rt_math_ceil` |
| C-MIG-0026 | `convert.i64_to_text` | `rt_raw_i64_to_string` |
| C-MIG-0028 | `encoding.byte_char.byte_char` | `rt_byte_char` |
| C-MIG-0019 | `time_utils.timestamp_from_components` | `rt_timestamp_from_components` |
| C-MIG-0019 | `time_utils.timestamp_add_days` | `rt_timestamp_add_days` |
| C-MIG-0019 | `time_utils.timestamp_diff_days` | `rt_timestamp_diff_days` |
| C-MIG-0019 | `time_utils.timestamp_get_year` | `rt_timestamp_get_year` |
| C-MIG-0019 | `time_utils.timestamp_get_month` | `rt_timestamp_get_month` |
| C-MIG-0019 | `time_utils.timestamp_get_day` | `rt_timestamp_get_day` |
| C-MIG-0020 | `hash.rt_hash_text` (ABI bridge) | `rt_hash_text` |
| C-MIG-0021 | `text.parse_i64` (well-formed input only — sentinel differs, see spec comment) | `rt_string_to_int` |
| C-MIG-0022 | `base_encoding.utilities.validated_utf8_bytes_to_text_linear` | `rt_text_validate_utf8` |

## Deferred pairs (not wired, with reasons)

| C-MIG id | Simple replacement | Reason deferred |
|---|---|---|
| C-MIG-0001 | `gzip.crc32_text` | file under concurrent edit (`gzip/**`) |
| C-MIG-0020 (`rt_str_hash`) | `hash.rt_hash_text` | `rt_str_hash` is not registered in the interpreter's extern dispatch table (`semantic: unknown extern function: rt_str_hash`) |
| C-MIG-0023 | `base_encoding.base64.{base64url_encode,base64url_decode}` | file under concurrent edit (`base_encoding/**`) |
| C-MIG-0024 | `string_core.str_last_index_of` | file under concurrent edit (`string_core.spl`) |
| C-MIG-0025 | `string_core.str_ends_with` | file under concurrent edit (`string_core.spl`) |
| C-MIG-0027 | `string_core.char_from_code` | file under concurrent edit (`string_core.spl`) |
| C-MIG-0029 | `math.special.sqrt_f64` | file under concurrent edit (`math/special.spl`) |
| C-MIG-0030 | `math.cbrt.cbrt_f64` | file under concurrent edit (`math/cbrt.spl`) |
| C-MIG-0033 | `numeric_round.is_nan_f64` | file under concurrent edit (`numeric_round.spl`, beyond the two pre-existing floor/ceil pairs) |
| C-MIG-0034 | `numeric_round.is_inf_f64` | file under concurrent edit (`numeric_round.spl`) |
| C-MIG-0035 | `text_ascii.to_upper_ascii` | file under concurrent edit (`text_ascii.spl`) |
| C-MIG-0036 | `path_pure.path_ext` | file under concurrent edit (`path_pure.spl`) |
| C-MIG-0013 | n/a | classified `partially_dead`/deleted — no live Simple replacement to dual-run |
| C-MIG-0016 | n/a | `conformance_oracle`, `replacement: none_needed` |

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
check current state before reusing): `path_pure.spl`, `text_ascii.spl`,
`text_builder.spl`, `math/special.spl`, `math/cbrt.spl`,
`numeric_round.spl` (beyond the pre-existing floor/ceil pairs),
`base_encoding/**` (beyond `utilities.spl`'s UTF-8 validator, wired above),
`gzip/**`, `string_core.spl`, `spec/evidence/**`.

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
