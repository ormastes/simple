# T32 MCP Server Bug Fixes — Plan

## Objective

Fix 10 categories of bugs in the T32 MCP server and CLI, with reproduction tests for each.

## Current Status

| Component | Status | Evidence |
|-----------|--------|----------|
| t32_mcp/session_tools.spl | Real (buggy) | Shell injection in t32_run_remote, blind CMM exec |
| t32_mcp/action_tools.spl | Real (buggy) | Parallel arrays, unescaped field names |
| t32_mcp/window_tools.spl | Real (buggy) | Hardcoded catalog path, no env override |
| t32_mcp/headless_tools.spl | Real (buggy) | Unvalidated area_name |
| t32_mcp/main.spl | Real (buggy) | Shutdown doesn't break loop |
| t32_mcp/json_helpers.spl | Real (buggy) | Port parsing, no validation |
| t32_cli/cli_shell.spl | Stub | cmm/set/do print messages but don't execute |
| test/feature/app/t32_tools/t32_mcp_spec.spl | Real | JSON/protocol tests only |

## What To Do

### Bug 1: Shell Injection in t32_run_remote (difficulty: 3)

**Problem:** `session_tools.spl:85-101` — `host`, `intercom_name`, and `cmd` are concatenated
into a shell command string passed to `/bin/sh -c`. An attacker-controlled `host` like
`localhost; rm -rf /` executes arbitrary commands.

**Fix:** Add `t32_shell_escape(s)` function in `json_helpers.spl` that wraps values in
single quotes and escapes embedded single quotes (`'` → `'\''`). Apply to `host`,
`intercom_name` in `t32_run_remote` and `t32_run_remote_timed`. The `cmd` parameter
is intentionally a T32 command so it passes through, but `host`/`port`/`intercom` are
user-supplied connection parameters that must be escaped.

**Test:** Verify that a host containing `; echo INJECTED` does NOT produce "INJECTED" in output.

### Bug 2: Blind CMM Execution (difficulty: 2)

**Problem:** `session_tools.spl:379-449` — `handle_t32_cmm_run` passes `script` directly
to `DO <script>` without checking:
- File extension is `.cmm`
- Path doesn't contain shell metacharacters
- Path exists on disk (optional — T32 may have its own fs)

**Fix:** Add validation in `handle_t32_cmm_run`:
1. Reject paths containing `;`, `|`, `&`, `` ` ``, `$`, `(`, `)`, `>`, `<`
2. Warn (but allow) if extension is not `.cmm`
3. Shell-escape the script path in the DO command

**Test:** Verify that `script: "test.cmm; rm -rf /"` is rejected with error.

### Bug 3: CLI Dispatching Missing (difficulty: 2)

**Problem:** `t32_cli/cli_shell.spl` — `shell_cmm`, `shell_set`, `shell_do` only print
messages but don't actually call `t32_run_remote` to execute commands on the T32 instance.

**Fix:** Wire the CLI shell commands to actually call the T32 backend:
- `shell_cmm` → call `t32_run_remote(session, "DO " + path)`
- `shell_set` → call `t32_run_remote(session, set_cmd)` using `t32_field_to_set_cmd`
- `shell_do` → call `t32_run_remote(session, action_template)`

**Test:** Verify that `shell_dispatch("cmm test.cmm")` produces a command string
that includes "DO test.cmm" (unit-level, no real T32 needed).

### Bug 3a: Missing `mcp-t32` CLI Subcommand (difficulty: 1)

**Problem:** `bin/simple mcp-t32` falls through to "file not found" because there is no
`case "mcp-t32"` in `src/app/cli/main.spl`, no entry in `dispatch/table.spl`, and no
`cli_run_mcp_t32` handler in `cli_commands.spl`.

**Fix:**
1. Add `fn cli_run_mcp_t32(args)` to `src/app/io/cli_commands.spl` — runs `./bin/t32_mcp_server.spl` via shell (model after `cli_run_mcp`)
2. Add `case "mcp-t32":` to `src/app/cli/main.spl` after `case "mcp":`
3. Add `CommandEntry(name: "mcp-t32", ...)` to `src/app/cli/dispatch/table.spl`

### Bug 3b: `t32_find_backend()` Missing WSL Support (difficulty: 2)

**Problem:** `session_tools.spl:43-78` only checks Linux-native paths. Under WSL,
T32 is typically installed at `C:\T32` which maps to `/mnt/c/T32/`. No WSL detection,
no Windows-style candidate paths.

**Fix:**
1. Add `t32_is_wsl()` helper: check if `/proc/version` contains "microsoft" or "WSL"
2. When WSL detected, add candidate paths:
   - `/mnt/c/T32/bin/windows64/t32rem.exe`
   - `/mnt/c/T32/bin/t32rem.exe`
3. If `T32MEM` is set, also derive WSL paths from it

### Bug 3c: No `T32MEM` Env Var for Path Configuration (difficulty: 2)

**Problem:** Only `T32REM` (explicit binary path) and `T32_PYTHON_BRIDGE` env vars exist.
No way to set the T32 installation root so all candidate paths derive from it.

**Fix:**
1. Check `T32MEM` env var in `t32_find_backend()` before hardcoded paths
2. When set, derive candidates: `T32MEM + "/bin/pc_linux64/t32rem"`, `T32MEM + "/bin/t32rem"`
3. Under WSL, also try `T32MEM + "/bin/windows64/t32rem.exe"`

### Bug 4: Multi-Core Issues (difficulty: 2)

**Problem:** `session_tools.spl:282-333` — `handle_t32_core_list`:
1. Accepts `session_id` param but ignores it (line 286 calls `t32_find_current_session()`)
2. Falls back to 1 core silently if EVAL fails
3. No error returned to caller on failure

**Fix:**
1. Use the `session_id` parameter to find the session (if provided)
2. Include a warning field in the response when falling back to 1 core
3. Add `core_select` validation: reject non-existent core IDs

**Test:** Verify that passing `session_id` actually uses that session.
Verify fallback includes `"warning":"core_query_failed"`.

### Bug 5: Catalog Hardcoded (difficulty: 2)

**Problem:** `window_tools.spl:13-24` — SDN catalog path is hardcoded as relative
`config/t32/catalogs/windows.sdn`. No env var override, no error logging when file
not found.

**Fix:**
1. Check `T32_CATALOG_DIR` env var first, fall back to `config/t32/catalogs`
2. Log to stderr when SDN file not found (diagnostic, not error)
3. Same for actions.sdn and fields.sdn

**Test:** Verify that setting `T32_CATALOG_DIR` env var changes the load path.

### Bug 6: Variable Read — No Input Escaping (difficulty: 3)

**Problem:** `action_tools.spl:137-168` — `t32_field_to_eval` maps field keys to
EVAL expressions without escaping. A field key like `var.x; QUIT` would produce
`Var.VALUE(x; QUIT)` which could be exploited.

**Fix:** Add `t32_validate_identifier(name)` that rejects names containing
shell metacharacters (`;`, `|`, `&`, `$`, `` ` ``, `(`, `)`, `>`, `<`, `{`, `}`, space).
Apply in `t32_field_to_eval` and `t32_field_to_set_cmd` before building commands.
Same for `memory.ADDR` — validate hex format.

**Test:** Verify `t32_field_to_eval("var.x; QUIT")` returns an error or empty string.
Verify `t32_field_to_eval("memory.0xDEADBEEF")` works.
Verify `t32_field_to_eval("memory.not_hex!")` is rejected.

### Bug 7: WEL/AREA Paths (difficulty: 2)

**Problem:**
- `headless_tools.spl:84` — `area_name` from user input goes directly into
  `WinPrint.AREA <area_name>` command
- `window_tools.spl:393` — Predictable `/tmp/t32_capture_<key>.txt` path
  (symlink attack surface)

**Fix:**
1. Validate `area_name` with `t32_validate_identifier` (alphanumeric + underscore only)
2. Use randomized temp file names: `/tmp/t32_<random>_<key>.txt`
   (use `rt_time_now_unix_micros()` as suffix for uniqueness)

**Test:** Verify area_name with spaces/semicolons is rejected.
Verify temp file path contains timestamp component.

### Bug 8: Validation Gaps (difficulty: 2)

**Problem:**
- `session_tools.spl:191-199` — Port parsing manually loops chars, caps at 10,
  doesn't validate non-digit characters (e.g., "200abc" → 200)
- `t32_extract_field` returns "" for both "missing key" and "empty value"

**Fix:**
1. Port parsing: after loop, verify entire string was consumed (all digits).
   Reject non-numeric port strings with error.
2. Add `t32_is_all_digits(s)` validation helper.

**Test:** Verify `port: "20000"` works.
Verify `port: "abc"` returns error.
Verify `port: "200; echo"` returns error.

### Bug 9: Data Structures (difficulty: 2)

**Problem:**
- Parallel arrays `MCP_T32_FIELD_STATE` + `MCP_T32_FIELD_VALUES` are fragile
  (index sync, O(n) lookup)
- History capping: `[250..]` drops oldest 250 entries at threshold 500 — arbitrary

**Fix:**
1. Replace parallel arrays with single array of `"key=value"` entries
   (or keep parallel arrays but document the invariant and add bounds check)
2. History: use sliding window — drop oldest 1 entry when at cap instead of bulk drop
   (change `[250..]` to `[1..]` at cap 500)

**Test:** Verify field state set/get round-trips correctly.
Verify history keeps last N entries correctly.

### Bug 10: Shutdown (difficulty: 1)

**Problem:** `main.spl:104-105` — `shutdown` method returns a result but the
`while true` loop continues reading the next message. Per MCP spec, after shutdown
response the server should exit.

**Fix:**
1. After sending shutdown response, `return` from `t32_start_server`
2. Before returning, close any open sessions (send cleanup commands)
3. Clean up AREA buffer if `MCP_T32_AREA_READY`

**Test:** Verify shutdown method causes server loop to exit.
Verify cleanup is attempted for open sessions.

## Task Dependencies (DAG)

```
Bug1 (shell escape) ──┬── Bug2 (CMM validation) uses shell_escape
                       ├── Bug6 (field validation) uses validate_identifier
                       └── Bug7 (AREA validation) uses validate_identifier
Bug8 (port validation) ── independent
Bug3 (CLI dispatch) ── independent
Bug4 (multi-core) ── independent
Bug5 (catalog env) ── independent
Bug9 (data structures) ── independent
Bug10 (shutdown) ── independent
```

**Critical path:** Bug1 → Bug2, Bug6, Bug7 (these depend on the escape/validation helpers)

## Test Strategy

All tests go in `test/feature/app/t32_tools/t32_mcp_bugfix_spec.spl`.
Tests are pure-function unit tests where possible (no real T32 connection needed).
Tests that need session state use mock sessions with `McpT32Session(...)` constructor.
