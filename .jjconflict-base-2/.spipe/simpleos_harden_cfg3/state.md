# CFG3 — second non-IDE consumer of std.config (P7 resume step)

Date: 2026-07-27
Lane: CFG3 (SimpleOS production-harden parallel campaign)
Status: DONE (all specs green; coordinator to land)

## Chosen consumer

`std.test_runner.test_config` (src/lib/nogc_sync_mut/test_runner/test_config.spl)
— the test runner's TestConfig. Why: it was the only surveyed candidate with a
genuine hand-rolled LAYERED merge (compiled-default table + config/simple.test.sdn
document + CI env override), including a per-key `match` ladder, `to_int_or` /
`parse_f64_or` fallback chains, a private `key: value` line parser duplicating
config_core's, and a duplicated defaults table. Bonus: the old ladder carried a
CONFIRMED defect (apply_test_config_value missing `mut` — every file key was a
silent no-op; doc/08_tracking/bug/test_config_apply_value_missing_mut_param_2026-07-17.md).
Routing through config_core deletes the defect class.

Sites surveyed and rejected (no real layered merge): src/app/mcp/** (scattered
single env_get reads), src/app/cli/** (simple.sdn manifest I/O, not layered),
src/app/build/cli_entry.spl, src/lib/nogc_sync_mut/ui/theme_package.spl
(registry lookup + single default fallback), ui/session.spl, ui/access_store.spl.
_make_daemon_config in test_runner_main.spl is a 3-field struct copy over the
now-config_core-backed TestConfig — left as-is (not a merge engine).

## Layer mapping

compiled_default = TestConfig schema defaults (single source; old defaults table
deleted — TestConfig.defaults() = test_config_resolve([])).
workspace = config/simple.test.sdn document (nested test:/cpu_throttle:/
session_max_sessions: sections flattened onto canonical schema keys).
session = CI env override (CI=true/1 → ci_mode/run_slow_tests/fail_fast).
mandatory = policy ceiling (spec-proven: pins timeout/memory against over-limit
session/workspace values; config_is_locked reports true).

## Behaviour kept identical

load_test_config_from_path keeps its pre-existing deterministic-startup gate
(early return of compiled defaults). Enabling the (now unit-proven) file parse
is a separate decision — the checked-in simple.test.sdn would flip parallel=true,
timeout=120, throttling on for every runner invocation.

## config_core API additions (minimal)

- schema.spl: `config_f64_field`, `config_is_f64_text`, "f64" branch in
  `config_validate_value` (cpu_threshold/memory_threshold are f64).
- layers.spl: `config_strip_inline_comment` (simple.test.sdn allows trailing
  `# comments`; kept opt-in so flat-document callers keep exact semantics).

## Deleted (the point of the lane)

to_int_or, parse_f64, parse_f64_or, parse_config_key_value,
apply_test_config_value (defective), parse_test_config_content,
_apply_session_max, and the literal defaults table — ~190 lines of hand-rolled
merge replaced by ~150 lines of schema declaration + section flattening that
delegate precedence/validation/conversion to config_core. Net on the module:
338 → 313 lines with strictly more behaviour (validation, mandatory ceiling).

## Evidence (build/cfg3_job = bin/release/x86_64-unknown-linux-gnu/simple)

- test/01_unit/lib/test_runner/test_config_spec.spl — 10 examples, 0 failures
  (defaults absolute values; workspace-over-default; CI session-over-workspace;
  mandatory ceiling clamps 6000→90 and 999999→512 with locked=true; malformed /
  below-min values fall back).
- test/01_unit/lib/common/config_core/config_layers_spec.spl — 33 examples,
  0 failures (was 31/0 baseline; +2 for f64 + comment-strip coverage).
- test/01_unit/app/test_runner_new/test_config_spec.spl — 6 + 3 examples,
  0 failures (was BROKEN at baseline: imported nonexistent
  app.test_runner_new.test_config; repointed to std.test_runner).
- test/01_unit/app/test_runner_new/test_config_float_fallback_spec.spl —
  1 example, 0 failures (was broken import at baseline).
- test/01_unit/app/test_runner_new/test_config_numeric_guard_spec.spl —
  1 example, 0 failures (was 1/1 FAILING at baseline: source-pinned a deleted
  file path; now pins the config_core guard).

## Landmine hit and survived

A parallel-session working-copy reconcile clobbered this lane's uncommitted
edits TWICE (files reverted to origin content minutes after green runs; no git
stash held them). Countermeasure that worked: re-apply, then immediately run
`jj status` so jj snapshots the WC — post-snapshot the files survived spec runs.
Coordinator: verify markers before landing (grep test_config_resolve in
test_config.spl = 3; config_f64_field in schema.spl = 1).

## Files changed

- src/lib/common/config_core/schema.spl (f64 support)
- src/lib/common/config_core/layers.spl (config_strip_inline_comment)
- src/lib/nogc_sync_mut/test_runner/test_config.spl (rewrite on config_core)
- test/01_unit/lib/test_runner/test_config_spec.spl (rewritten, 10 examples)
- test/01_unit/lib/common/config_core/config_layers_spec.spl (+2 examples)
- test/01_unit/app/test_runner_new/test_config_spec.spl (repaired + updated)
- test/01_unit/app/test_runner_new/test_config_float_fallback_spec.spl (repaired)
- test/01_unit/app/test_runner_new/test_config_numeric_guard_spec.spl (repaired)
- doc/08_tracking/os/production_status.sdn (config row note only)
- .spipe/simpleos_harden_cfg3/state.md (this file)
