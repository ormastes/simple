# MCP Command-Line Handshake

> Build and launch the pure-Simple MCP server, send real MCP `initialize`, `notifications/initialized`, and `tools/list` JSONL frames, and require a bounded response. Then call `simple_pipe` and `simple_search`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Command-Line Handshake

Build and launch the pure-Simple MCP server, send real MCP `initialize`, `notifications/initialized`, and `tools/list` JSONL frames, and require a bounded response. Then call `simple_pipe` and `simple_search`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/app/build/bootstrap.md |
| Plan | doc/03_plan/sys_test/mcp_cmdline_handshake.md |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl` |
| Updated | 2026-07-15 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Build and launch the pure-Simple MCP server, send real MCP
`initialize`, `notifications/initialized`, and `tools/list` JSONL frames,
and require a bounded response. Then call `simple_pipe` and `simple_search`.

## Examples

`simple_mcp_server` must identify `Simple MCP Server`, list `simple_pipe`,
report `spipe: linked`, and return a bounded no-match search result.

## Scenarios

### Pure-Simple MCP Launch and Handshake

### REQ-MCP-CMD-001: pure-Simple MCP answers real stdio handshakes

#### should build the exact MCP artifact with pure Stage 2

- Strictly native-build src/app/mcp/main.spl with pure Stage 2
   - Expected: build_exit equals `0`
   - Expected: file_exists(pure_simple_mcp_binary()) is true
   - Expected: build_stderr does not contain `stub fallback`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Strictly native-build src/app/mcp/main.spl with pure Stage 2")
val (_, build_stderr, build_exit) = build_pure_simple_mcp()
expect(build_exit).to_equal(0)
expect(file_exists(pure_simple_mcp_binary())).to_equal(true)
expect(build_stderr.contains("stub fallback")).to_equal(false)
```

</details>

#### should launch the exact MCP artifact and list Simple tools within the time limit

- Run the Stage 2-built MCP artifact with initialize and tools/list frames
- Require readiness, successful exit, bounded latency, and simple_pipe
   - Expected: probe.ok is true
   - Expected: probe.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run the Stage 2-built MCP artifact with initialize and tools/list frames")
val probe = mcp_cmdline_probe("simple_mcp", pure_simple_mcp_binary(), 15, 15000, "Simple MCP Server", "simple_pipe", "", "")
step("Require readiness, successful exit, bounded latency, and simple_pipe")
expect(probe.ok).to_equal(true)
expect(probe.exit_code).to_equal(0)
expect(probe.elapsed_ms).to_be_less_than(15001)
expect(probe.ready_json).to_contain("Simple MCP Server")
expect(probe.stdout).to_contain("simple_pipe")
```

</details>

#### should run core Simple MCP features without source or Rust fallback

- Launch the cached native Simple MCP artifact
- mcp tool call frame
- mcp tool call frame
- Check the linked SPipe surface and bounded empty search result
   - Expected: probe.ok is true
   - Expected: probe.stderr does not contain `bootstrap-only`
   - Expected: probe.stderr does not contain `mode=source`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Launch the cached native Simple MCP artifact")
val calls = (
    mcp_tool_call_frame("3", "simple_pipe", "{\"surface\":\"spipe\"}") +
    mcp_tool_call_frame("4", "simple_search", "{\"query\":\"__PURE_SIMPLE_MCP_SANITY_NO_MATCH__\",\"scope\":\"src\"}")
)
val probe = mcp_cmdline_probe("simple_mcp_features", pure_simple_mcp_binary(), 15, 15000, "Simple MCP Server", "simple_search", calls, "status: ready")
step("Check the linked SPipe surface and bounded empty search result")
expect(probe.ok).to_equal(true)
expect(probe.stdout).to_contain("spipe: linked")
expect(probe.stdout).to_contain("No results found.")
expect(probe.stderr.contains("bootstrap-only")).to_equal(false)
expect(probe.stderr.contains("mode=source")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/app/build/bootstrap.md`
- **Plan:** `doc/03_plan/sys_test/mcp_cmdline_handshake.md`


</details>
