# simple_visibility MCP tool: make_tool_error arity bug (fixed) + child run still failing under spec

- Date: 2026-10-26 | Owner area: src/app/mcp/main_lazy_diag_tools.spl, main_lazy_json.spl shell_cmd | Size: S + unknown
- Symptom: test/01_unit/app/mcp/mcp_visibility_requester_spec.spl 4/6 fail with
  `semantic: in call to make_tool_error (declared at line 315): function expects argument for parameter 'msg'`.
- Root cause 1 (product, FIXED in worktree): make_tool_error(id, code, msg) (main_lazy_json.spl:316) called without
  `code` at main_lazy_diag_tools.spl:275 and :288. Added `-32603`.
- Root cause 2 (OPEN): after the fix the handler returns the new error "Could not compute visibility for: ... (requester ...)":
  `shell_cmd("timeout 30 <bin> run src/app/cli/query_visibility.spl visibility ...")` (main_lazy_diag_tools.spl:285-286,
  shell_cmd main_lazy_json.spl:417) returns non-zero/empty in-process although the same command run by hand in Git Bash
  exits 0 in 1.3 s with valid JSON. Setting SIMPLE_BINARY did not help. Suspect Windows shell selection
  (_get_shell cmd vs sh: single-quoted args `'file'`/`'requester'` are literal under cmd.exe, timeout prefix stripped).
  Spec result after fix: 2 pass, 4 fail (now with ERROR -32603 payload).
- Repro: `bin/simple.exe test test/01_unit/app/mcp/mcp_visibility_requester_spec.spl --no-session-daemon`

## Resolution (2026-10-27)
- Root cause 2: `shell_cmd` built a single shell string (`timeout 30 <bin> run ... '<file>' ... 2>/dev/null`) and
  ran it via cmd/sh; under the spec's in-process Windows environment the shell selection/quoting/`timeout`
  prefix broke the child. The working sibling (`src/app/simple_lsp_mcp/tools.spl`) uses literal argv.
- Fix: `handle_simple_visibility` and `handle_simple_symbols` (src/app/mcp/main_lazy_diag_tools.spl) now call
  `mcp_run_argv(_bin, ["run", "src/app/cli/query_visibility.spl", ...], 30000, 262144)` (no shell, no quoting).
- Result: mcp_visibility_requester_spec 2/6 -> 6/6; lsp_visibility_requester_spec 5/5 (unchanged).
- Note: `mcp_run_argv` merges stderr into output (the old command dropped it via `2>/dev/null`).

## Correction (review of PR #4957)
The landed fix calls `process_run_bounded` directly with literal argv and keeps stdout only, matching the old `2>/dev/null`. It does not use `mcp_run_argv`, which merges stderr into the output.
