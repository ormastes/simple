# Bug: `bin/simple check` rejects SSpec `describe`/`it` DSL files

Date: 2026-06-28
Status: fixed for text output in source; focused execution pending a fresh pure-Simple runtime
Owner: compiler / SSpec tooling

## Summary

`bin/simple check` is not a valid syntax gate for SSpec scenario files that use
the `std.spec` `describe` / `it` DSL. It reports parser errors on the DSL colon
tokens before reaching the helper functions in the file.

## Observed Command

```sh
SIMPLE_LIB=src bin/simple check test/03_system/check/gui_web_2d_goal_completion_criteria_spec.spl
```

## Observed Result

The command ran for roughly 90 seconds on this host, then failed with parser
errors like:

```text
[parser_error] line 219:47: unexpected token in expression: : ':'
[parser_error_ctx] path test/03_system/check/gui_web_2d_goal_completion_criteria_spec.spl kind 161 text ':'
```

Line 219 is the ordinary SSpec form:

```simple
describe "GUI/Web/2D goal completion criteria":
```

## Impact

Agents may waste time rerunning a slow invalid check and incorrectly treat a
valid SSpec file as syntactically broken. For SSpec files, use the SSpec runner
or focused wrapper guards instead of `bin/simple check` until this is fixed.

## Expected Behavior

One of these should become true:

- `bin/simple check` understands SSpec `describe` / `it` syntax, or
- `bin/simple check` detects SSpec DSL files and emits a fast actionable message
  directing users to `bin/simple test ... --mode=interpreter`.

## Current Workaround

For the GUI/Web/2D completion checklist, use:

```sh
sh scripts/check/check-gui-web-2d-completion-criteria-placeholders.shs
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_renderdoc_aggregate_cache_modes_spec.spl --mode=interpreter --clean --fail-fast
```

Do not run the full GUI/Web/2D completion SSpec on a headless host expecting a
pass; it is intentionally a native-platform completion gate.

## Related Cleanup

`doc/07_guide/app/mcp/mcp.md` was updated to use `bin/simple test ... --mode=interpreter`
for the MCP command-line handshake SSpec instead of `bin/simple check`.

## Source fix (2026-07-15)

Both pure-Simple check entrypoints now share one bounded SSpec source detector
for text output. A file with a column-zero `std.spec` import and a top-level
`describe ...:` block returns the documented actionable `bin/simple test
<path> --mode=interpreter` guidance before invoking the general parser. The
detector ignores triple-string bodies, indented text, and import-name prefixes;
JSON behavior and general parser grammar are unchanged.
`test/02_integration/app/check_log_modes_spec.spl` guards the standalone check
entry, rejects the former generic colon-token diagnostic, and covers those
negative cases.
