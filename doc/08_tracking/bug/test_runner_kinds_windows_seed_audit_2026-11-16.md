# Test runner kind audit on Windows with the Rust seed (2026-11-16)

Status: open (findings below), 2 small fixes landed in the same PR
Binary: `C:/dev/simple/bin/simple.exe`, 37622272 bytes, mtime Nov 12 21:49,
`Simple Language v1.0.0-rc.1` (Rust bootstrap seed, prints the seed warning).
Tree: origin/release/1.0.0 `00a5a1d3401`. No bug_db.sdn rows are added (seal
conflicts with other open PRs); this file is the record.

## Fixed in this PR
1. `--compile=<mode>` (documented in `simple test --help`) was rejected with
   `Error: unknown option: --compile=smf` (rc=2). The validator
   (`src/lib/nogc_sync_mut/test_runner/test_runner_args.spl`) and the app parser
   (`src/app/test_runner_new/test_runner_args.spl`) knew only bare `--compile`.
   Repro/generalization: `test/01_unit/lib/nogc_sync_mut/test_runner/compile_equals_mode_arg_spec.spl`
   (1 pass / 2 fail before, 3 pass after). `test ... --compile=smf --keep-artifacts` rc 2 -> 0.
2. `std.test_runner.test_executor_parsing` (nogc_async_mut twin) did not
   re-export `parse_blocked_examples`; `test_runner_single.spl` imported it
   (`[use-warning] ... does not provide it`). Also two private fns the existing
   `blocked_outcome_spec.spl` imports (`verdict_outcome_token`,
   `test_db_file_row_from_result`) were not `pub`. Spec went from
   `executed=0` (rc 1) to `executed=12 passed=12` (rc 0).

## Open, not fixed here (each needs more than a minimal runner edit)
- `--list-runs`, `--cleanup-runs`, `--prune-runs`: `handle_run_management` in
  `src/app/test_runner_new/test_runner_config.spl:122` (and the
  `src/lib/nogc_sync_mut/test_runner` twin at :358) is a stub printing
  `DISABLED: handle_run_management (memory debug)` and returning 1; the real body
  is commented out ("uses GROUP 4", test_db_compat). Restoring it means
  re-enabling the GROUP 4 DB import the stub was added to avoid.
- `--format sdn` (the replacement for retired `--format json`) fails on the seed
  with `SDN worker scoped-environment process provider is unavailable or
  insufficient` (`sdn_wrapper.spl:256`, needs the V4 process-observation provider
  of the native runtime). `--format json` is retired
  (`ERROR: JSON test output is retired; use --format sdn`) but the seed `--help`
  (Rust) and `doc/07_guide/infra/testing.md` still advertise `json`.
- Single-file route ignores filter/layer flags: `--list`, `--list-ignored`,
  `--only-skipped`, `--fuzz`, `--chaos`, `--deploy`, `--security` on one spec
  all just execute it normally (rc 0, plain verdict, no fuzz/chaos/deploy/security
  output). `--list <dir>` does list ("Discovered N test file(s)", file-level only).
- `test query ...` on the seed prints the `test` usage and exits 0 (no query
  subcommand); `.shs`/`.pl`/`.ps1` files under `test/00_unit/scripts` are not
  discovered by `simple test <file>` (rc 4, "No SPL files with doctests found");
  they are plain scripts to run with `sh`/`perl`/`powershell`.
- Seed parse failure of `src/compiler/00.common/driver_compile_options.spl:63`
  already filed: `seed_parse_multiline_list_driver_compile_options_2026-11-15.md`
  (blocks `test/05_perf/interp/push_call_loop_env_cache_spec.spl`, executed=0).
- Host/seed limits, real RED: `test/02_integration/lib/sosix/memory_executable_native_spec.spl`
  (`OwnedProcessV3 opaque adapter is unavailable in the interpreter`),
  `test/05_perf/app/debug/debug_service_v1_perf_spec.spl:84`
  (`unknown property or method 'nil' on Option`),
  `test/02_integration/app/add_remove_log_modes_spec.spl` ("supports add log-mode json":
  expected `"constraint":"^1.0.0"`, got `1.0.0`).
