# Anti-Dummy / Anti-Stub Enforcement Report

**Date:** 2026-04-04  
**Updated:** 2026-04-04 (P2 T32 hardware specs cleaned)  
**Status:** Implemented on all active public-facing surfaces

## What Was Added

- `STUB003` denies explicit `pass_todo(...)` placeholders in production code.
- `SSPEC004` denies print-based skip placeholders in specs/examples.
- `SSPEC005` denies examples that have no real assertion or sanctioned `skip:`.
- `SSPEC006` denies boolean-wrapper assertions such as `expect(a != b).to_equal(true)`.
- the pure-Simple lint path now uses the real `Linter` result stream instead of only fix-rule output.
- the compiled Rust CLI now applies the same quality checks through:
  - `simple lint`
  - `simple verify quality`

## Files Changed

- [main.spl](src/compiler/90.tools/lint/main.spl)
- [stub_impl.spl](src/compiler/35.semantics/lint/stub_impl.spl)
- [test_quality_gate.spl](src/app/verify/test_quality_gate.spl)
- [cli_commands.spl](src/app/io/cli_commands.spl)
- [lint_entry.spl](src/app/cli/lint_entry.spl)
- [sspec_quality_lint_spec.spl](test/integration/app/sspec_quality_lint_spec.spl)
- [verify_test_quality_gate_spec.spl](test/integration/app/verify_test_quality_gate_spec.spl)
- [code_quality.rs](src/compiler_rust/driver/src/cli/code_quality.rs)
- [verify.rs](src/compiler_rust/driver/src/cli/verify.rs)
- [help.rs](src/compiler_rust/driver/src/cli/help.rs)
- [anti_dummy_quality_cli_tests.rs](src/compiler_rust/driver/tests/anti_dummy_quality_cli_tests.rs)
- [lint.md](doc/07_guide/tooling/lint.md)

## Verification

Passed:

- `./bin/simple check src/compiler/35.semantics/lint/stub_impl.spl src/compiler/90.tools/lint/main.spl src/app/verify/test_quality_gate.spl src/app/verify/main.spl test/integration/app/sspec_quality_lint_spec.spl test/integration/app/verify_test_quality_gate_spec.spl test/unit/compiler/lint/stub_impl_spec.spl`
- `./bin/simple test test/integration/app/sspec_quality_lint_spec.spl`
- `./bin/simple test test/integration/app/verify_test_quality_gate_spec.spl`
- `./bin/simple test test/unit/compiler/lint/stub_impl_spec.spl`
- `cargo test -p simple-driver --test anti_dummy_quality_cli_tests -- --nocapture`
- `./bin/simple lint /tmp/bad_quality_spec.spl` -> `SSPEC006`
- `./bin/simple verify quality /tmp/placeholder_spec.spl` -> fails with `SSPEC002` and `SSPEC005`
- `./bin/simple verify quality /tmp/good_spec.spl` -> passes

## Research Basis

- test smell detection as a structural analysis problem:
  - https://testsmells.org/assets/publications/EASE2021_TechnicalPaper.pdf
- explicit failure-path assertion guidance:
  - https://docs.junit.org/5.0.1/user-guide/index.pdf
- mutation testing as a stronger later-stage verifier:
  - https://pitest.org/

## Remaining Debt

- a tree-wide grep still finds many legacy placeholder patterns in `src/` and `test/`
- mutation-style verification has not yet been added
- some source-entry wrappers still have their own interpreter-path issues, but the installed compiled CLI path is now closed

## Public-Surface Cleanup

The following public-facing proof surfaces now pass the compiled quality gate:

- `test/integration/sffi/direction_a_c_roundtrip_spec.spl`
- `test/integration/sffi/direction_a_cpp_roundtrip_spec.spl`
- `test/integration/sffi/direction_b_import_roundtrip_spec.spl`
- `test/integration/sffi/callback_roundtrip_spec.spl`
- `test/integration/sffi/layout_verification_roundtrip_spec.spl`
- `test/system/sffi_bidirectional_interop_spec.spl`
- `test/integration/t32_hw/22_action_list_invoke_spec.spl`
- `test/integration/t32_hw/23_screenshot_spec.spl`
- `test/integration/t32_hw/30_dialog_tools_spec.spl`
- `test/system/async_promise_system_spec.spl`
- `src/compiler/90.tools/async_integration.spl`
- `test/integration/t32_hw/02_t32_open_close_spec.spl`
- `test/integration/t32_hw/10_session_open_spec.spl`
- `test/integration/t32_hw/11_session_list_info_spec.spl`
- `test/integration/t32_hw/12_core_tools_spec.spl`
- `test/integration/t32_hw/13_cmd_run_spec.spl`
- `test/integration/t32_hw/14_cmm_run_spec.spl`
- `test/integration/t32_hw/15_eval_spec.spl`
- `test/integration/t32_hw/16_error_check_spec.spl`
- `test/integration/t32_hw/17_window_list_describe_spec.spl`
- `test/integration/t32_hw/18_window_open_capture_spec.spl`
- `test/integration/t32_hw/20_power_cycle_for_new_spec.spl`
- `test/integration/t32_hw/21_field_get_set_spec.spl`
- `test/integration/t32_hw/24_history_tail_spec.spl`
- `test/integration/t32_hw/26_cmm_commands_validate_spec.spl`
- `test/integration/t32_hw/27_area_read_spec.spl`
- `test/integration/t32_hw/28_setup_headless_spec.spl`

## Repo Debt Snapshot

Representative remaining placeholder-heavy areas from the 2026-04-04 audit:

- `src/os/posix/`
- `src/os/tools/`
- `src/lib/gc_async_mut/gpu/`
- `src/os/userlib/`
- legacy spec buckets under `test/specs/`, `test/app/`, and hardware-oriented integration suites

These no longer block the enforcement feature itself, but they still block a truthful “universal repo-wide cleanliness” claim.

## P2 Cleanup (T32 Hardware Specs)

All 16 T32 hardware specs in `test/integration/t32_hw/` have been cleaned:

- `02_t32_open_close_spec.spl` — 2 placeholders replaced
- `10_session_open_spec.spl` — 1 placeholder replaced
- `11_session_list_info_spec.spl` — 2 placeholders replaced
- `12_core_tools_spec.spl` — 3 placeholders replaced
- `13_cmd_run_spec.spl` — 5 placeholders replaced
- `14_cmm_run_spec.spl` — 3 placeholders replaced
- `15_eval_spec.spl` — multiple placeholders replaced
- `16_error_check_spec.spl` — 2 placeholders replaced
- `17_window_list_describe_spec.spl` — 3 placeholders replaced
- `18_window_open_capture_spec.spl` — 1 placeholder replaced
- `20_power_cycle_for_new_spec.spl` — 2 placeholders replaced
- `21_field_get_set_spec.spl` — 1 placeholder replaced
- `24_history_tail_spec.spl` — multiple placeholders replaced
- `26_cmm_commands_validate_spec.spl` — multiple placeholders replaced
- `27_area_read_spec.spl` — multiple placeholders replaced
- `28_setup_headless_spec.spl` — 3 pass_do_nothing + expect(true) replaced

## Practical Status

The feature is now implemented on both the source and compiled CLI paths. All active public-facing proof surfaces are clean. Remaining debt is only in deferred/experimental/postponed areas (OS, GPU, archived specs). It should be described as:

- `Implemented`
