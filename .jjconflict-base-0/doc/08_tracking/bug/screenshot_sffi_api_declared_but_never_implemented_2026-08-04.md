# `std.spec.screenshot` SFFI API is declared but implemented nowhere

**Status:** OPEN
**Found:** 2026-08-04

## Symptom

Every function in the screenshot capture API fails at call time because the
`rt_screenshot_*` externs behind it do not exist in any runtime.

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test \
    test/02_integration/lib/std/screenshot/screenshot_ffi_spec.spl --no-cache
  ✗ enables and disables screenshot capture
      semantic: unknown extern function: rt_screenshot_disable
  ✗ sets refresh mode
      semantic: unknown extern function: rt_screenshot_set_refresh
  ✗ sets output directory
      semantic: unknown extern function: rt_screenshot_set_output_dir
  ✗ sets and clears test context
      semantic: unknown extern function: rt_screenshot_set_context
Results: 11 total, 0 passed, 11 failed
```

Expected: the 11 examples exercise enable/disable, refresh mode, output
directory, test context, path generation, and before/after terminal capture.

## Root cause

Two independent defects stacked, which is why this read as a naming problem at
first.

1. **Rename drift (fixed).** The module at
   `src/compiler_rust/lib/std/src/spec/screenshot.spl:56-94` exports
   `enable_sffi_screenshots`, `set_sffi_refresh`, `set_sffi_output_dir`,
   `set_sffi_test_context`, `capture_before_sffi`, … (SFFI), while the spec
   still called the pre-rename `_ffi_` names. Those resolved to nothing, so the
   failures read `function 'enable_ffi_screenshots' not found` and masked
   defect 2 entirely. The spec's call names were updated to the module's actual
   exports; every assertion is unchanged. (`screenshot_exists_ffi` genuinely
   keeps the `_ffi` spelling — the module is internally inconsistent.)

2. **The API is dead (NOT fixed).** With the names corrected, the calls reach
   their externs and die there. `rt_screenshot_disable`,
   `rt_screenshot_set_refresh`, `rt_screenshot_set_output_dir`,
   `rt_screenshot_set_context` and siblings are declared in
   `src/compiler_rust/lib/std/src/spec/screenshot.spl` and are implemented in
   **neither** `src/runtime/` nor `src/compiler_rust/compiler/src/` — a
   recursive grep for `rt_screenshot_disable` across both trees returns nothing.
   The whole screenshot capture feature is a declaration surface with no
   implementation behind it.

## Why not fixed now

Closing it means writing the `rt_screenshot_*` runtime primitives (terminal
buffer capture to disk, output-dir and test-context state, path generation).
That is a new runtime feature in C/Rust, not a defect repair, and it lands in
seed-bundled runtime code that repo rules keep off-limits to this lane
("Fix .spl not Rust"; seed is bootstrap-only).

The spec was left asserting the real API and therefore still red — deliberately.
Deleting or skipping it would erase the only record that this feature is
unimplemented.

## Related

- `interpreter_extern_registry_gap_blocks_os_specs_2026-08-04.md` — sibling
  lane, externs that exist in the C runtime but are missing from the
  *interpreter's* registry. This one is the stronger case: the symbols exist
  nowhere at all.
