# Browser Script Execution Not Wired

**Date:** 2026-05-10
**Component:** browser_engine/browser_renderer.spl, script/script_runner.spl
**Severity:** Medium (feature gap)
**Status:** Partially resolved (2026-05-10)

## Problem

Simple scripts in `<script type="text/simple">` tags were parsed but never
executed. Three independent blockers prevented end-to-end script execution.

## Blockers

### 1. Renderer Discards Script Content — RESOLVED
`browser_renderer.spl` now imports `html_tree_builder_build_with_scripts` and
`TreeBuilderResult`. New `browser_renderer_parse_html_with_scripts()` exposes
script collection. New `render_html_to_pixels_with_scripts()` integrates
rendering with script collection and execution.

### 2. ScriptHost/ScriptRunner Never Invoked — RESOLVED
`render_html_to_pixels_with_scripts()` creates a `ScriptHost`, executes
collected inline scripts via `host.execute()` and external scripts via
`host.execute_file()`, and captures console output into `BeScriptRenderResult`.

### 3. interpret_file Unavailable in Interpreter Mode — RESOLVED (subprocess)
`run_script()` now uses `rt_process_run("bin/simple", ["run", tmp_path])` instead
of the broken `use lazy compiler.driver.driver_api_interpret.{interpret_file}`.
Scripts execute in a subprocess. Console stdout is captured into ConsoleBuffer.

**Remaining limitation:** DOM mutations from scripts do not cross the process
boundary. Scripts can validate parsing and produce console output, but cannot
modify the rendered DOM tree. Full in-process execution requires a future
`rt_interpret_file` runtime extern.

## Test Coverage
- `test/unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_script_spec.spl` — 6 tests

## Related
- `script_runner.spl` f-string parse bug: fixed (commit a3c, 2026-05-10)
- Color commonization blocked: `browser_color_commonization_blocked_2026-05-10.md`
