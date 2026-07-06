# Claude In Chrome MCP Server

> Checks MCP DebugLogger level mapping.

<!-- sdn-diagram:id=mcpServer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcpServer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcpServer_spec -> std
mcpServer_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcpServer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude In Chrome MCP Server

Checks MCP DebugLogger level mapping.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/claudeInChrome/mcpServer_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks MCP DebugLogger level mapping.

## Scenarios

### Claude in Chrome MCP server

#### should map logger methods to debug levels

- var logger = DebugLogger new
   - Expected: logger.entries[0].level equals `debug`
   - Expected: logger.entries[1].level equals `debug`
   - Expected: logger.entries[2].level equals `info`
   - Expected: logger.entries[3].level equals `warn`
   - Expected: logger.entries[4].level equals `error`
   - Expected: logger.entries[4].message equals `error`
   - Expected: mcpServerSourceLinesModeled() equals `293`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var logger = DebugLogger.new().silly("trace").debug("debug").info("info").warn("warn").error("error")
expect(logger.entries[0].level).to_equal("debug")
expect(logger.entries[1].level).to_equal("debug")
expect(logger.entries[2].level).to_equal("info")
expect(logger.entries[3].level).to_equal("warn")
expect(logger.entries[4].level).to_equal("error")
expect(logger.entries[4].message).to_equal("error")
expect(mcpServerSourceLinesModeled()).to_equal(293)
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
