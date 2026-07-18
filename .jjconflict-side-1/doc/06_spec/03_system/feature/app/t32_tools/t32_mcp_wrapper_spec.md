# T32 MCP Wrapper -- Cold tools/call regression

> Verifies that the wrapper can handle `initialize` followed by a real

<!-- sdn-diagram:id=t32_mcp_wrapper_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_mcp_wrapper_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_mcp_wrapper_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_mcp_wrapper_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 MCP Wrapper -- Cold tools/call regression

Verifies that the wrapper can handle `initialize` followed by a real

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/feature/app/t32_tools/t32_mcp_wrapper_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies that the wrapper can handle `initialize` followed by a real
`tools/call` for `t32_sessions_list` without tripping the RSS watchdog.

## Scenarios

### T32 MCP Wrapper

#### handles initialize plus t32_sessions_list without RSS timeout

1. rt file delete
   - Expected: result.exit_code equals `0`
   - Expected: stdout contains `"id":"1"`
   - Expected: stdout contains `"id":"2"`
   - Expected: stdout contains `"items":[]`
   - Expected: stdout contains `"target_state":"unknown"`
   - Expected: stdout does not contain `[watchdog] RSS`
   - Expected: stderr does not contain `[watchdog] RSS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mk_input = shell("mktemp /tmp/t32_mcp_input.XXXXXX")
val input_path = (mk_input.stdout ?? "").trim()
val messages = init_request("1") + tools_call_request("2", "t32_sessions_list", "{}")
expect(input_path != "").to_equal(true)
expect(rt_file_write_text(input_path, messages)).to_equal(true)

val cmd = "timeout 20s /home/ormastes/dev/pub/simple/bin/t32_mcp_server < " + shell_escape_text(input_path)
val result = shell(cmd)
val stdout = result.stdout ?? ""
val stderr = result.stderr ?? ""

rt_file_delete(input_path)

expect(result.exit_code).to_equal(0)
expect(stdout.contains("\"id\":\"1\"")).to_equal(true)
expect(stdout.contains("\"id\":\"2\"")).to_equal(true)
expect(stdout.contains("\"items\":[]")).to_equal(true)
expect(stdout.contains("\"target_state\":\"unknown\"")).to_equal(true)
expect(stdout.contains("[watchdog] RSS")).to_equal(false)
expect(stderr.contains("[watchdog] RSS")).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
