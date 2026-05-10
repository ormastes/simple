# Browser Script Execution Not Wired

**Date:** 2026-05-10
**Component:** browser_engine/browser_renderer.spl, script/script_runner.spl
**Severity:** Medium (feature gap)
**Status:** Open

## Problem

Simple scripts in `<script type="text/simple">` tags are parsed but never
executed. Three independent blockers prevent end-to-end script execution.

## Blockers

### 1. Renderer Discards Script Content
`browser_renderer.spl` lines 3460-3471 detect `<script>` tags but skip their
content entirely. The hand-written HTML parser in `browser_renderer_html_string_to_dom()`
does not collect script bodies.

Note: `html_tree_builder.spl` has `html_tree_builder_build_with_scripts()` which
properly collects script bodies and src paths into `TreeBuilderResult.scripts`
and `TreeBuilderResult.src_paths`, but `browser_renderer.spl` uses its own
parser instead.

### 2. ScriptHost/ScriptRunner Never Invoked
No render pipeline method calls ScriptHost or ScriptRunner. The script
infrastructure exists (ScriptHost, ScriptRunner, EventLoop, ConsoleBuffer,
all API modules) but is not wired into the render flow.

### 3. interpret_file Unavailable in Interpreter Mode
`run_script()` uses `use lazy compiler.driver.driver_api_interpret.{interpret_file}`
to execute wrapped scripts. The `compiler.*` namespace is not resolvable when
running under the interpreter, so this call fails with "function not found".

## Resolution Path

1. Either switch `browser_renderer.spl` to use `html_tree_builder_build_with_scripts()`
   or add script collection to the existing hand-written parser
2. Wire ScriptHost into the render pipeline (after layout, before paint
   or as a post-render step)
3. For blocker 3, either:
   a. Add an `rt_interpret_file(path)` runtime extern (bypasses compiler namespace)
   b. Require compiled mode for script execution
   c. Use a different execution strategy (eval-style extern)

## Related
- `script_runner.spl` f-string parse bug: fixed (commit a3c, 2026-05-10)
- Color commonization blocked: `browser_color_commonization_blocked_2026-05-10.md`
