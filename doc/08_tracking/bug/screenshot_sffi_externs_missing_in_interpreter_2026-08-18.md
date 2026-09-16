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

## Resolution (2026-08-18)
FIXED in source (seed-resident; this lane does not deploy `bin/simple`).

Added `src/compiler_rust/compiler/src/interpreter_extern/screenshot_sffi.rs`,
registered as `pub mod screenshot_sffi;` and via 16 `insert_simple!` entries in
`interpreter_extern/mod.rs`. The handlers delegate to the real runtime
(`simple_runtime::value::screenshot_sffi`, already a dependency of the compiler
crate — same pattern as `interpreter_extern/atomic.rs`), so the interpret and
native lanes share one implementation and one piece of state. Symbols wired:
enable, disable, is_enabled, set_refresh, is_refresh, set_output_dir,
get_output_dir, set_context, clear_context, clear_captures,
capture_before_terminal, capture_after_terminal, exists, get_path,
capture_count, free_string.

Headless: none of these needs a display — terminal capture writes the ANSI
buffer to a text file under the output dir, so the family works headless.

Evidence (private build at /mnt/data/tmp/shotfix/release/simple; RED baseline
/mnt/data/tmp/classfix/release/simple):
- `test/{02_,}integration/lib/std/screenshot/screenshot_ffi_spec.spl`
  RED   `Results: 11 total, 0 passed, 11 failed` (`unknown extern function: rt_screenshot_enable`)
  GREEN `Results: 11 total, 10 passed, 1 failed`
- new `screenshot_sffi_extern_dispatch_spec.spl` (both test trees)
  RED   `Results: 5 total, 0 passed, 5 failed`
  GREEN `Results: 5 total, 5 passed, 0 failed`

The one remaining failure is an UNRELATED parser defect, not a screenshot gap:
`expect exists == false` fails with ``semantic: variable `expect` not found``
whenever the local is named `exists`. Tracked in
`doc/08_tracking/bug/expect_before_identifier_named_exists_2026-08-18.md`.
