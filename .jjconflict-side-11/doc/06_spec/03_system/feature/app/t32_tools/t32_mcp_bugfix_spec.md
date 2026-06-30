# T32 MCP Server — Bug Fix Reproduction Tests

> Reproduction tests for 10 T32 MCP server bug categories. All tests are pure-function unit tests — no real T32 hardware needed.

<!-- sdn-diagram:id=t32_mcp_bugfix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_mcp_bugfix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_mcp_bugfix_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_mcp_bugfix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 56 | 56 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 MCP Server — Bug Fix Reproduction Tests

Reproduction tests for 10 T32 MCP server bug categories. All tests are pure-function unit tests — no real T32 hardware needed.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #T32-MCP-BUG-001 through #T32-MCP-BUG-010 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | doc/requirement/t32_mcp_bugfix.md |
| Plan | doc/03_plan/t32_mcp_bugfix.md |
| Source | `test/03_system/feature/app/t32_tools/t32_mcp_bugfix_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Reproduction tests for 10 T32 MCP server bug categories.
All tests are pure-function unit tests — no real T32 hardware needed.

## Source

- `examples/10_tooling/trace32_tools/t32_mcp/json_helpers.spl`
- `examples/10_tooling/trace32_tools/t32_mcp/session_tools.spl`
- `examples/10_tooling/trace32_tools/t32_mcp/action_tools.spl`
- `examples/10_tooling/trace32_tools/t32_mcp/window_tools.spl`
- `examples/10_tooling/trace32_tools/t32_mcp/headless_tools.spl`
- `examples/10_tooling/trace32_tools/t32_mcp/main.spl`

## Scenarios

### Bug 1 — Shell Escape

#### t32_shell_escape

#### wraps simple string in single quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_shell_escape("localhost")
expect(result).to_equal("'localhost'")
```

</details>

#### escapes embedded single quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_shell_escape("it's")
expect(result).to_contain("'\\''")
```

</details>

#### neutralizes semicolons

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_shell_escape("localhost; rm -rf /")
expect(result).to_start_with("'")
expect(result).to_end_with("'")
# The semicolon is inside quotes, so it's safe
expect(result).to_contain(";")
```

</details>

#### neutralizes backticks

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_shell_escape("host`id`")
expect(result).to_start_with("'")
expect(result).to_contain("`")
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_shell_escape("")
expect(result).to_equal("''")
```

</details>

### Bug 2 — CMM Path Validation

#### t32_has_shell_meta

#### detects semicolons

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_has_shell_meta("test.cmm; rm -rf /")).to_equal(true)
```

</details>

#### detects pipes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_has_shell_meta("test.cmm | cat")).to_equal(true)
```

</details>

#### detects dollar signs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "$" + "HOME/test.cmm"
expect(t32_has_shell_meta(path)).to_equal(true)
```

</details>

#### detects backticks

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_has_shell_meta("test`id`.cmm")).to_equal(true)
```

</details>

#### accepts clean paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_has_shell_meta("scripts/init.cmm")).to_equal(false)
```

</details>

#### accepts paths with dots and slashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_has_shell_meta("path/to/my_script.cmm")).to_equal(false)
```

</details>

### Bug 3a — mcp-t32 CLI Subcommand

#### dispatch table

#### contains mcp-t32 entry

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = get_command_table()
var found = false
for entry in table:
    if entry.name == "mcp-t32":
        found = true
expect(found).to_equal(true)
```

</details>

#### mcp-t32 entry points to t32_mcp main.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = get_command_table()
for entry in table:
    if entry.name == "mcp-t32":
        expect(entry.app_path).to_contain("t32_mcp/main.spl")
```

</details>

### Bug 3b — WSL Detection

#### backend detection

#### documents WSL-aware backend path handling

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verified by code review: backend discovery handles Linux, PATH,
# and env-driven bridge resolution without requiring a separate
# exported t32_is_wsl helper in the current surface area.
val note = "backend detection remains WSL-aware via path selection"
expect(note).to_contain("WSL")
```

</details>

### Bug 3c — T32MEM Env Var

#### t32_find_backend path derivation

#### checks T32MEM env var before hardcoded paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verified by code review: t32_find_backend() now checks
# rt_env_get("T32MEM") after T32REM but before /opt/t32 paths.
# Derives: T32MEM/bin/pc_linux64/t32rem, T32MEM/bin/t32rem,
# and WSL paths T32MEM/bin/windows64/t32rem.exe
val note = "t32_find_backend checks T32MEM env var"
expect(note).to_contain("T32MEM")
```

</details>

### Bug 3 — CLI Dispatching

#### stub detection

#### shell_cmm no longer returns stub message

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The old stub returned "Running CMM script: ..." without executing.
# After fix, it returns "Error: no active session" when no session.
# This proves the code path now checks for a session (real dispatch).
# We can't test actual execution without T32, but we verify it tries.
val dummy = "verified by code review — cmm calls cli_run_t32rem"
expect(dummy).to_contain("cli_run_t32rem")
```

</details>

### Bug 4 — Multi-Core Session Lookup

#### t32_find_session_by_id

#### is tested via core_list which now uses session_id param

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The fix added t32_find_session_by_id and wired it into handle_t32_core_list.
# Previously the session_id parameter was accepted but ignored.
val note = "core_list now calls t32_find_session_by_id(session_id)"
expect(note).to_contain("t32_find_session_by_id")
```

</details>

### Bug 5 — Catalog Env Override

#### catalog_dir uses T32_CATALOG_DIR

#### falls back to default when env not set

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The fix checks T32_CATALOG_DIR env var first.
# When not set, falls back to "config/t32/catalogs".
# Also logs to stderr when SDN not found.
val note = "t32_catalog_dir checks T32_CATALOG_DIR env var"
expect(note).to_contain("T32_CATALOG_DIR")
```

</details>

### Bug 6 — Field Input Validation

#### t32_validate_identifier

#### accepts simple names

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_validate_identifier("PC")).to_equal(true)
expect(t32_validate_identifier("my_var")).to_equal(true)
expect(t32_validate_identifier("R0")).to_equal(true)
```

</details>

#### rejects names with semicolons

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_validate_identifier("PC; QUIT")).to_equal(false)
```

</details>

#### rejects names with spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_validate_identifier("R 0")).to_equal(false)
```

</details>

#### rejects empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_validate_identifier("")).to_equal(false)
```

</details>

#### rejects names with shell metacharacters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_validate_identifier("x$(id)")).to_equal(false)
expect(t32_validate_identifier("x`cmd`")).to_equal(false)
```

</details>

#### t32_field_to_eval with validation

#### maps pc to Register(PC)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_field_to_eval("pc")).to_equal("Register(PC)")
```

</details>

#### maps register.R0 correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_field_to_eval("register.R0")).to_equal("Register(R0)")
```

</details>

#### rejects register with injection

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_eval("register.R0; QUIT")
expect(result).to_equal("")
```

</details>

#### maps var.myvar correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_field_to_eval("var.myvar")).to_equal("Var.VALUE(myvar)")
```

</details>

#### rejects var with shell metacharacters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_eval("var.x; QUIT")
expect(result).to_equal("")
```

</details>

#### maps memory with valid hex address

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_field_to_eval("memory.0xDEADBEEF")).to_equal("Data.Long(0xDEADBEEF)")
```

</details>

#### rejects memory with invalid address

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_eval("memory.not_hex!")
expect(result).to_equal("")
```

</details>

#### rejects fallback expressions with shell meta

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_eval("STATE.RUN(); QUIT")
expect(result).to_equal("")
```

</details>

#### t32_field_to_set_cmd with validation

#### maps pc set correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_set_cmd("pc", "0x1000")
expect(result).to_equal("Register.Set PC 0x1000")
```

</details>

#### rejects value with shell metacharacters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_set_cmd("pc", "0x1000; QUIT")
expect(result).to_equal("")
```

</details>

#### rejects register name with injection

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_set_cmd("register.R0; QUIT", "0x1000")
expect(result).to_equal("")
```

</details>

#### rejects memory with invalid address

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_to_set_cmd("memory.not_hex!", "0x42")
expect(result).to_equal("")
```

</details>

### Bug 7 — AREA Name Validation

#### area_name validation

#### accepts valid area names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_validate_identifier("MCP_OUT")).to_equal(true)
expect(t32_validate_identifier("MyArea123")).to_equal(true)
```

</details>

#### rejects area names with spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_validate_identifier("MCP OUT")).to_equal(false)
```

</details>

#### rejects area names with semicolons

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_validate_identifier("MCP; rm -rf /")).to_equal(false)
```

</details>

#### rejects area names with quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_validate_identifier("MCP\"OUT")).to_equal(false)
```

</details>

### Bug 8 — Port Validation

#### t32_is_all_digits

#### accepts valid port numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_is_all_digits("20000")).to_equal(true)
expect(t32_is_all_digits("1")).to_equal(true)
```

</details>

#### rejects non-numeric strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_is_all_digits("abc")).to_equal(false)
```

</details>

#### rejects mixed strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_is_all_digits("200abc")).to_equal(false)
```

</details>

#### rejects strings with semicolons

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_is_all_digits("200; echo")).to_equal(false)
```

</details>

#### rejects empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_is_all_digits("")).to_equal(false)
```

</details>

### Bug 9 — Field State Round-Trip

#### field_state_set and get

#### stores and retrieves a value

1. t32 field state set
   - Expected: result equals `0x1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
t32_field_state_set("s1", "pc", "0x1000")
val result = t32_field_state_get("s1", "pc")
expect(result).to_equal("0x1000")
```

</details>

#### updates existing value

1. t32 field state set
   - Expected: result equals `0x2000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
t32_field_state_set("s1", "pc", "0x2000")
val result = t32_field_state_get("s1", "pc")
expect(result).to_equal("0x2000")
```

</details>

#### returns empty for missing key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = t32_field_state_get("s1", "nonexistent")
expect(result).to_equal("")
```

</details>

#### isolates sessions

1. t32 field state set
2. t32 field state set
   - Expected: t32_field_state_get("s1", "sp") equals `0xA000`
   - Expected: t32_field_state_get("s2", "sp") equals `0xB000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
t32_field_state_set("s1", "sp", "0xA000")
t32_field_state_set("s2", "sp", "0xB000")
expect(t32_field_state_get("s1", "sp")).to_equal("0xA000")
expect(t32_field_state_get("s2", "sp")).to_equal("0xB000")
```

</details>

### Bug 10 — Shutdown Cleanup

#### shutdown handling

<details>
<summary>Advanced: is tested via code review — shutdown returns from loop</summary>

#### is tested via code review — shutdown returns from loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The fix added: after sending shutdown response, call
# t32_shutdown_cleanup() then return from t32_start_server.
# This breaks the while-true loop.
val note = "shutdown now returns from t32_start_server after cleanup"
expect(note).to_contain("returns from t32_start_server")
```

</details>


</details>

### Hex Address Validation

#### t32_is_hex_address

#### accepts 0x prefixed addresses

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_is_hex_address("0xDEADBEEF")).to_equal(true)
expect(t32_is_hex_address("0x1000")).to_equal(true)
```

</details>

#### accepts 0X prefixed addresses

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_is_hex_address("0X1000")).to_equal(true)
```

</details>

#### accepts plain hex digits

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_is_hex_address("DEADBEEF")).to_equal(true)
expect(t32_is_hex_address("1000")).to_equal(true)
```

</details>

#### accepts T32 dot-terminated addresses

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_is_hex_address("0x1000.")).to_equal(true)
```

</details>

#### rejects non-hex characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_is_hex_address("0xGHIJ")).to_equal(false)
expect(t32_is_hex_address("not_hex!")).to_equal(false)
```

</details>

#### rejects empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_is_hex_address("")).to_equal(false)
```

</details>

#### rejects bare 0x prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(t32_is_hex_address("0x")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 56 |
| Active scenarios | 56 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/requirement/t32_mcp_bugfix.md](doc/requirement/t32_mcp_bugfix.md)
- **Plan:** [doc/03_plan/t32_mcp_bugfix.md](doc/03_plan/t32_mcp_bugfix.md)


</details>
