# Bug: `bin/simple check` rejects SSpec `describe`/`it` DSL files

Date: 2026-06-28
Status: fixed (2026-11-11 runner10 lane — `check` now detects SSpec DSL files and emits the fast actionable message; expected-behavior option 2)
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

## 2026-11-11 — runner10 lane verdict: FIXED (option 2 of the row's Expected Behavior)

Source-verified at base 79d5af6723f6:

- `src/app/cli/check.spl:269-273` — `_check_path` now calls
  `check_sspec_guidance(source, path)` BEFORE parsing; on a non-empty result
  it prints the guidance and returns 1 (no raw parser-error spam, no
  90-second parse walk into DSL colon tokens).
- `src/app/check/sspec_source.spl:21-43` — `check_sspec_guidance` detects a
  spec file by `use std.spec` import + a top-level `describe ...:` line
  (docstring/comment aware via the shared CoreLexer string-state helpers) and
  emits exactly the actionable message the row asked for:
  `error[E-SSPEC-CHECK]: SSpec command-block files must use `bin/simple test
  <path> --mode=interpreter``.
- Landed via merge 9e7e7a526edb (PR #7597, 2026-11-07; `git log` on
  `src/app/check/sspec_source.spl`). `check` is pure-Simple and runs from
  source under the tracked seed, so the fix is live at this base.
- Existing regression coverage:
  `test/01_unit/app/check/check_sspec_guidance_shared_lexer_spec.spl`
  exercises the guidance mechanism (including its triple-quote-in-comment
  defect replay over the spec corpus).

The exact observed command from this row
(`bin/simple check test/03_system/check/gui_web_2d_goal_completion_criteria_spec.spl`)
was NOT re-executed this lane (session died mid-flight; campaign no-rerun
rule); the flip rests on the unambiguous in-tree source plus the existing
spec coverage above.
