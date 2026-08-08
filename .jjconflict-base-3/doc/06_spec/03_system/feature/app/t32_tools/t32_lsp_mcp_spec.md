# T32 LSP MCP Server -- CMM Intelligence Tests

> Tests for the T32 LSP MCP server: text utility functions (split, extract), CLI validation helpers (GUI keyword detection, command check), and JSON encoding/extraction from the LSP JSON helpers module.

<!-- sdn-diagram:id=t32_lsp_mcp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_lsp_mcp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_lsp_mcp_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_lsp_mcp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 LSP MCP Server -- CMM Intelligence Tests

Tests for the T32 LSP MCP server: text utility functions (split, extract), CLI validation helpers (GUI keyword detection, command check), and JSON encoding/extraction from the LSP JSON helpers module.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #T32-LSP-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/app/t32_tools/t32_lsp_mcp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for the T32 LSP MCP server: text utility functions (split, extract),
CLI validation helpers (GUI keyword detection, command check),
and JSON encoding/extraction from the LSP JSON helpers module.

## Source

`examples/10_tooling/trace32_tools/t32_lsp_mcp/tools.spl`
`examples/10_tooling/trace32_tools/t32_lsp_mcp/json_helpers.spl`

## Scenarios

### T32 LSP MCP Text Utilities

#### split_to_lines

#### splits multiline string

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = split_to_lines("line1\nline2\nline3")
expect(lines[0]).to_equal("line1")
expect(lines.len()).to_equal(3)
expect(lines[1]).to_equal("line2")
expect(lines[2]).to_equal("line3")
```

</details>

#### handles single line

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = split_to_lines("hello")
expect(lines[0]).to_equal("hello")
expect(lines.len()).to_equal(1)
```

</details>

#### handles empty string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = split_to_lines("")
expect(lines[0]).to_equal("")
expect(lines.len()).to_equal(1)
```

</details>

#### extract_word_at

#### extracts word at start

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val word = extract_word_at("BREAK.Set 0x1000", 3)
expect(word).to_equal("BREAK.Set")
```

</details>

#### extracts word in middle

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val word = extract_word_at("Data.dump 0x1000", 5)
expect(word).to_equal("Data.dump")
```

</details>

#### returns empty for out-of-bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val word = extract_word_at("hello", -1)
expect(word).to_equal("")
```

</details>

#### stops at delimiters

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val word = extract_word_at("fn(arg1, arg2)", 3)
expect(word).to_equal("arg1")
```

</details>

### T32 LSP MCP CLI Validation

#### GUI keyword detection

#### detects dialog keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val violations = check_gui_keywords("DIALOG.view test.dlg")
expect(violations[0]).to_equal("dialog")
expect(violations.len()).to_be_greater_than(0)
```

</details>

#### detects winpos keyword

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val violations = check_gui_keywords("WinPOS 0 0 80 40")
expect(violations[0]).to_equal("winpos")
expect(violations.len()).to_be_greater_than(0)
```

</details>

#### returns empty for clean CLI script

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "SCREEN.OFF\nAREA.Create A000\nAREA.Select A000\nBREAK.Set 0x1000"
val violations = check_gui_keywords(script)
expect(violations.len()).to_equal(0)
```

</details>

#### ignores comments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val violations = check_gui_keywords("; dialog is fine in comments")
expect(violations.len()).to_equal(0)
```

</details>

#### ignores labels ending with colon

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val violations = check_gui_keywords("dialog_closed:")
expect(violations.len()).to_equal(0)
```

</details>

#### command detection

#### finds SCREEN.OFF

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "SCREEN.OFF\nBREAK.Set main\nGo"
val found = check_has_command(script, "screen.off")
expect(found).to_equal(true)
```

</details>

#### returns false when absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "BREAK.Set main\nGo"
val found = check_has_command(script, "screen.off")
expect(found).to_equal(false)
```

</details>

#### ignores commented-out commands

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = "; SCREEN.OFF\nBREAK.Set main"
val found = check_has_command(script, "screen.off")
expect(found).to_equal(false)
```

</details>

### T32 LSP MCP JSON Helpers

#### encoding

#### escapes special characters

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lsp_escape_json("a\"b\\c\nd")
expect(result).to_contain("\\\"")
expect(result).to_contain("\\\\")
expect(result).to_contain("\\n")
```

</details>

#### builds quoted string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lsp_js("test")
expect(result).to_equal("\"test\"")
```

</details>

#### builds key-value pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = lsp_jp("key", lsp_js("val"))
expect(result).to_equal("\"key\":\"val\"")
```

</details>

#### builds single-pair object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair = lsp_jp("x", lsp_js("1"))
val result = lsp_jo1(pair)
expect(result).to_equal("{\"x\":\"1\"}")
```

</details>

#### extraction

#### extracts field from JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"method\":\"initialize\",\"id\":1}"
val result = lsp_extract_field(json, "method")
expect(result).to_equal("initialize")
```

</details>

#### handles missing fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"a\":1}"
val result = lsp_extract_field(json, "missing")
expect(result).to_equal("")
```

</details>

### T32 LSP MCP Wrapper

#### recovers from stale ready marker before tools/call

1. rt file delete
2. shell
   - Expected: result.exit_code equals `0`
   - Expected: stdout contains `"id":"1"`
   - Expected: stdout contains `"id":"2"`
   - Expected: stdout contains `"result"`
   - Expected: stdout does not contain `Tool daemon timed out`
   - Expected: stdout contains `failed to become ready`
   - Expected: stderr does not contain `Transport closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mk_input = shell("mktemp /tmp/t32_lsp_mcp_input.XXXXXX")
val input_path = (mk_input.stdout ?? "").trim()
val daemon_dir = "/tmp/t32_lsp_mcp_spec_stale_ready"
val stale_req = daemon_dir + "/stale.req"
val messages = init_request("1") + tools_call_request("2", "cmm_complete", "{\"source\":\"BR\",\"line\":0,\"character\":2}") + shutdown_request("3")
expect(input_path != "").to_equal(true)
expect(rt_file_write_text(input_path, messages)).to_equal(true)

val setup = shell("rm -rf " + shell_escape_text(daemon_dir) + " && mkdir -p " + shell_escape_text(daemon_dir) + " && printf ready > " + shell_escape_text(daemon_dir + "/ready") + " && printf stale > " + shell_escape_text(stale_req))
expect(setup.exit_code).to_equal(0)

val cmd = "timeout 15s env T32_LSP_MCP_TOOL_DAEMON_DIR=" + shell_escape_text(daemon_dir) + " /home/ormastes/dev/pub/simple/bin/t32_lsp_mcp_server < " + shell_escape_text(input_path)
val result = shell(cmd)
val stdout = result.stdout ?? ""
val stderr = result.stderr ?? ""

rt_file_delete(input_path)
shell("rm -rf " + shell_escape_text(daemon_dir))

expect(result.exit_code).to_equal(0)
expect(stdout.contains("\"id\":\"1\"")).to_equal(true)
expect(stdout.contains("\"id\":\"2\"")).to_equal(true)
expect(stdout.contains("\"result\"")).to_equal(true)
expect(stdout.contains("Tool daemon timed out")).to_equal(false)
expect(stdout.contains("failed to become ready")).to_equal(true)
expect(stderr.contains("Transport closed")).to_equal(false)
```

</details>

#### passes escaped source text through tools/call arguments

1. rt file delete
2. shell
   - Expected: result.exit_code equals `0`
   - Expected: stdout contains `"id":"2"`
   - Expected: stdout does not contain `Missing required parameter: source`
   - Expected: stdout contains `"node_count"`
   - Expected: stderr does not contain `Transport closed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mk_input = shell("mktemp /tmp/t32_lsp_mcp_input.XXXXXX")
val input_path = (mk_input.stdout ?? "").trim()
val daemon_dir = "/tmp/t32_lsp_mcp_spec_escaped_source"
val args_json = "{\"source\":\"PRINT \\\"arguments\\\": 1\",\"line\":0,\"character\":0}"
val messages = init_request("1") + tools_call_request("2", "cmm_parse", args_json) + shutdown_request("3")
expect(input_path != "").to_equal(true)
expect(rt_file_write_text(input_path, messages)).to_equal(true)

val setup = shell("rm -rf " + shell_escape_text(daemon_dir))
expect(setup.exit_code).to_equal(0)

val cmd = "timeout 20s env SIMPLE_RUNTIME=" + shell_escape_text("/home/ormastes/dev/pub/simple/src/compiler_rust/target/debug/simple") + " T32_LSP_MCP_TOOL_DAEMON_DIR=" + shell_escape_text(daemon_dir) + " /home/ormastes/dev/pub/simple/bin/t32_lsp_mcp_server < " + shell_escape_text(input_path)
val result = shell(cmd)
val stdout = result.stdout ?? ""
val stderr = result.stderr ?? ""

rt_file_delete(input_path)
shell("rm -rf " + shell_escape_text(daemon_dir))

expect(result.exit_code).to_equal(0)
expect(stdout.contains("\"id\":\"2\"")).to_equal(true)
expect(stdout.contains("Missing required parameter: source")).to_equal(false)
expect(stdout.contains("\"node_count\"")).to_equal(true)
expect(stderr.contains("Transport closed")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
