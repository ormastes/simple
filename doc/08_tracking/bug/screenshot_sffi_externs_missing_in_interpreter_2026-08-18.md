# `rt_screenshot_*` externs unimplemented in the seed interpreter (2026-08-18)

## Status
OPEN — seed-resident, cannot be deployed from this lane.

## Symptom
`test/{02_,}integration/lib/std/screenshot/screenshot_ffi_spec.spl` failed with

    semantic: function `disable_ffi_screenshots` not found; semantic: function
    `set_ffi_refresh` not found; semantic: function `set_ffi_output_dir` not found

That first layer was a **stale test API**: `std.spec.screenshot`
(`src/compiler_rust/lib/std/src/spec/screenshot.spl`) renamed its control
surface `*_ffi_*` -> `*_sffi_*` (`enable_sffi_screenshots`,
`disable_sffi_screenshots`, `is_sffi_screenshots_enabled`, `set_sffi_refresh`,
`set_sffi_output_dir`, `set_sffi_test_context`, `clear_sffi_test_context`,
`clear_sffi_captures`, `capture_before_sffi`, `capture_after_sffi`,
`get_screenshot_path_sffi`; only `screenshot_exists_ffi` kept the old spelling).
The specs were retargeted to the current names.

## Remaining blocker (product side, seed-resident)
With the rename applied all 11 examples now fail one layer deeper:

    semantic: unknown extern function: rt_screenshot_enable
    semantic: unknown extern function: rt_screenshot_disable
    semantic: unknown extern function: rt_screenshot_set_refresh
    semantic: unknown extern function: rt_screenshot_set_output_dir
    semantic: unknown extern function: rt_screenshot_set_context

`rt_screenshot_*` IS implemented in the Rust runtime
(`src/compiler_rust/runtime/src/value/screenshot_sffi.rs`, re-exported from
`value/mod.rs`, listed in `common/src/runtime_symbols.rs`) but has **no handler
under `src/compiler_rust/compiler/src/interpreter_extern/`** — `grep -rl
rt_screenshot src/compiler_rust/compiler/src/interpreter_extern/` returns
nothing. The interpret lane, which is what `bin/simple test` uses, therefore
fails closed.

Fix requires adding an `interpreter_extern` module for the screenshot SFFI and
rebuilding the seed; this lane is forbidden from replacing `bin/simple`.

## Evidence
- RED (pre-rename): `Results: 11 total, 0 passed, 11 failed` —
  ``semantic: function `disable_ffi_screenshots` not found``
- POST-RENAME: `Results: 11 total, 0 passed, 11 failed` —
  `semantic: unknown extern function: rt_screenshot_enable`
