# Dual-run (C/Simple) shadow harness

## What this is

Two layers:

1. **The dual-run contract** (`src/lib/nogc_sync_mut/rt_hal/dual_runner.spl`,
   `virtual_device.spl`, `dual_run_ledger.spl`, design
   `doc/05_design/os/hal/asm_embedded_hal_and_dual_run.md` Part B): run the
   reference (C/asm twin) and the candidate (pure Simple) on the same typed
   arguments, write every output into a **per-provider shadow**, compare with
   a typed comparator, and only then commit ONE agreed copy to the real
   target — or trap. See "DualRunner contract" below.
2. **The legacy value-compare helper** (`src/lib/common/spec/dual_run.spl`,
   `dual_check_f64` / `dual_check_text`): after-the-fact comparison of two
   return values. Still the comparator for f64 inside the runner, and still
   what the 13 original pairs use (`mode=value-legacy`).

Both are goal 6 of the `binary_runtime_hardening` plan's Wave 4 ("a
framework that runs BOTH the C and Simple implementations at runtime") and
Phase 1 item 1.8/1.9 of `doc/03_plan/os/hal/asm_to_simple_migration_plan.md`.

## DualRunner contract

```
val r = DualRunner.create("<pair>", "<mode>", MismatchPolicy.Trap)
r.set_ledger(path)            # default build/dual_run/dual_run_ledger.sdn ($DUAL_RUN_LEDGER)
... one dual_run_* call per case ...
r.flush_ledger()              # one SDN row: pair, mode, run_id, cases, mismatches, first_mismatch_repr, binary_identity
```

| Mode | Call | Shadow target | Comparator | Commit on match |
|---|---|---|---|---|
| `value` | `dual_run_i64/f64/text(r, args, ref_fn, cand_fn[, bit_exact])` | return value | `==`, NaN-aware/bit-exact f64, text | the chosen value (`out.value`) |
| `shadow-buffer` | `dual_run_shadow_buffer(r, args, shadow: ShadowSet, ref_fn, cand_fn)` | `ShadowSet.from_real(name, real)`: `ref_copy` + `cand_copy` initialised from `real` | `compare_bytes` (first differing byte / length) | `shadow.real = chosen copy`, `shadow.commit_count += 1` |
| `shadow-state` | `dual_run_shadow_state(r, args, state: StateSnapshot, ref_fn, cand_fn, ignore)` | `StateSnapshot` (ordered field/value reprs) | `compare_struct` field-wise, `ignore` list for padding/timestamps | `out.state` = chosen snapshot; pre-op state survives a mismatch |
| `record-compare` | `dual_run_record_compare(r, args, ref_fn, cand_fn, read_script, poll_collapse, apply_hw)` / `dual_run_record_compare_trace(r, args, ref_trace, cand_fn, ...)` | `VirtualDevice` façade per provider (records `r|w<width>@addr=value`, answers reads from the script) | `effect_logs_compare` (ordered, optional poll collapse) | agreed log replayed once (`dual_apply_effects_mmio`) when `apply_hw`; `out.commit_writes`, `r.commit_count` |
| `replay` | `dual_run_replay(r, args, recorded, cand_fn, poll_collapse)` | candidate runs against the reference's recording (reads answered from it) | same | never — the reference's real run was the commit |

- **Argument transport:** `dual_args([arg_i64(..), arg_f64(..), arg_bool(..), arg_text(..), arg_bytes(..)])`,
  read back with `args_i64(a, i)` etc. Inputs are shared read-only; a provider
  that mutates one is a mismatch by construction. The compiler side
  (`validate_rt_hal_tags`) accepts exactly this set for `@rt(hal, c|rust)` fns.
- **Policy:** `Trap` (default in test lanes) commits nothing and marks the
  receipt `trapped`; `UseRef` commits the reference and still records the
  mismatch; `UseCandLog` is refused (traps) until `r.set_commit_from("cand")`,
  i.e. after the pair passed the soak bar.
- **Receipt:** `DualReceipt { pair, mode, args_repr, agree, ref_repr, cand_repr,
  committed, committed_from, trapped, policy, message }` — `message` names
  BOTH values (`MISMATCH <pair> ... ref=<..> cand=<..> (<detail>)`).
- **Ledger / soak:** `dual_ledger_load(path)`, `dual_ledger_soak(rows, pair)`
  → `SoakSummary { runs, cases, mismatches, identities, stable }` with the bar
  `SOAK_MIN_CASES=1000`, `SOAK_MIN_RUNS=30`, `SOAK_MIN_IDENTITIES=2`, 0
  mismatches. `run_id` comes from `$DUAL_RUN_ID` (the gate sets one per run),
  `binary_identity` from `$SIMPLE_BINARY_IDENTITY` (`unknown` otherwise).
- **Deliberate-mismatch fixtures** live in
  `test/01_unit/lib/nogc_sync_mut/rt_hal_dual_run_{shadow_buffer,record_compare}_spec.spl`
  and always use a temp ledger under `build/dual_run/spec_tmp/` — never the
  default one, which the gate reads.

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

## Pairs on the DualRunner contract (3, `test/01_unit/lib/common/spec/dual_run_pairs_spec.spl`)

| Pair | Mode | Reference | Candidate | Registry |
|---|---|---|---|---|
| `parse_i64_vs_rt_string_to_int` | `value` (text arg) | `rt_string_to_int` | `std.common.text.parse_i64` | C-MIG-0021 `dual_run_mode: value` |
| `base64url_decode_vs_rt_base64url_decode` | `shadow-buffer` (decode into a 32-byte target, one copy committed) | `rt_base64url_decode` | `std.common.base_encoding.base64.base64url_decode` | C-MIG-0023 `dual_run_mode: shadow-buffer` |
| `ns16550_putc_vs_log_write_byte_ns16550` | `record-compare` (poll LSR, write THR; `poll_collapse`) | `log_write_byte_ns16550` (`src/runtime/startup/baremetal/runtime_log.c:75`) — trace **derived from source**, not yet QEMU-captured | `std.nogc_sync_mut.rt_hal.ns16550_ops.ns16550_putc` | C-MIG-0043 `dual_run_mode: record-compare` |

## Adding a new pair

1. Pick an entry from `c_migration_inventory.sdn` and add
   `dual_run_mode: <mode>` + `dual_run_spec: <spec>` to it.
2. In a `*_spec.spl` under `test/`, add ONE annotation line per pair — this
   is what the gate enumerates, there is no hard-coded list:
   `# @dual_pair: <name> mode=<mode> ref=<C symbol> cand=<Simple fn> id=<C-MIG id>`
3. Write providers with the runner's signatures (`fn(DualArgs) -> i64`,
   `fn(DualArgs, [u8]) -> [u8]`, `fn(DualArgs, VirtualDevice)`, ...), declare
   the `extern fn rt_...` oracle in the spec, create a `DualRunner`, run
   representative + edge-case inputs, assert `receipt.agree` and
   `r.mismatches == 0`, and finish with `r.flush_ledger()` (default ledger —
   so every case here must agree; deliberate mismatches go to a temp ledger).
4. Run `bin/simple test <spec>` and `sh scripts/check/check-dual-run-shadow.shs`;
   the verdict must list your pair and stay `PASS`.

Areas to avoid (contested/in-flux at the time this harness was written —
check current state before reusing): `path_pure.spl`, `text_ascii.spl`,
`text_builder.spl`, `math/special.spl`, `math/cbrt.spl`,
`numeric_round.spl` (beyond the pre-existing floor/ceil pairs),
`base_encoding/**` (beyond `utilities.spl`'s UTF-8 validator, wired above),
`gzip/**`, `string_core.spl`, `spec/evidence/**`.

## Gate

`scripts/check/check-dual-run-shadow.shs` runs `--selftest` first (fatal, 7
fixtures: healthy / divergent / vacuous spec output, annotation enumeration,
0-pair tree → ERROR, ledger mismatch for the current run → FAIL, registry
`dual_run_mode:` rows), then:

1. enumerates every `# @dual_pair:` annotation under `test/` (0 → `ERROR`),
2. runs each annotated spec once with a private `DUAL_RUN_ID` and
   `DUAL_RUN_LEDGER` (default `build/dual_run/dual_run_ledger.sdn`),
3. reads back the ledger rows for that run: any `mismatches > 0` is a `FAIL`
   naming the pair and its `first_mismatch_repr`; a spec failure is a `FAIL`
   too; a spec with no `Results:` line is `ERROR`.

Verdict is the last stdout line:
`PASS — <n> pair(s) checked, <m> case(s) (+<k> ledger comparison(s)), 0 divergent`
/ `FAIL — ...` (exit 1) / `ERROR — nothing was checked` (exit 2).
Options: `--test-root`, `--registry`, `--ledger`, `--simple-bin`, `--selftest-only`.
Measured 2026-08-28 (seed binary): `PASS — 16 pair(s) checked, 18 case(s) (+20 ledger comparison(s)), 0 divergent`;
a mutated copy of the pairs spec (candidate returns 43 for "42") gives
`FAIL — 3 pair(s) checked, 3 case(s), ledger mismatch: parse_i64_vs_rt_string_to_int(1 mismatch(es): "ref=42 cand=43")`.

## Honest limitations

- **Test-lane only.** Both providers run inside specs on the inputs the
  author chose; no production call path dual-runs live traffic yet. The
  contract is the same one a production lane would use (`DualRunner` +
  `apply_hw`), but no lane sets `apply_hw = true` and nothing calls
  `dual_apply_effects_mmio` outside the runner.
- **C twins run in-process only through the interpreter's extern table.** A
  C function that writes raw volatile pointers (the ns16550 reference) cannot
  run against the façade; its trace is derived from source until a QEMU /
  board capture exists. The design's ≥ 10 clean QEMU record-compare runs per
  arch (B.8) are still owed — board-runnable rule applies.
- **Ledger path deviates from the design.** B.7 names
  `doc/08_tracking/hal/dual_run_ledger.sdn`; the implementation writes
  `build/dual_run/dual_run_ledger.sdn` (gitignored runtime state). Deliberate
  — update the design doc rather than the code.
- **The soak bar is future accumulation.** The ledger accounting and
  `stable` predicate are implemented and spec'd on synthesised rows; real
  rows so far come from single gate runs on one binary identity.
