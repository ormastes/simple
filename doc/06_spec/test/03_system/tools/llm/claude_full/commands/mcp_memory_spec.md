# Claude Full MCP and Memory Commands

> Checks modern SSpec parity for MCP command surface and memory descriptors.

<!-- sdn-diagram:id=mcp_memory_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_memory_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_memory_spec -> std
mcp_memory_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_memory_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full MCP and Memory Commands

Checks modern SSpec parity for MCP command surface and memory descriptors.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/commands/mcp_memory_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks modern SSpec parity for MCP command surface and memory descriptors.

## Scenarios

### Claude full mcp memory commands

#### should expose MCP command metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mcpCommandName()).to_equal("mcp")
expect(mcpCommand().description).to_contain("MCP")
expect(summarizeMcpServer(McpServerStatus.new("fs", "connected", "stdio"))).to_equal("fs:connected:stdio")
```

</details>

#### should expose memory command metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(memoryCommandName()).to_equal("memory")
expect(memoryTargetPath("project")).to_equal("CLAUDE.md")
expect(memoryTargetPath("user")).to_contain(".claude")
```

</details>

#### should expose source sizes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mcpSourceLinesModeled()).to_equal(84)
expect(mcpIndexSourceLinesModeled()).to_equal(12)
expect(memorySourceLinesModeled()).to_equal(89)
expect(memoryIndexSourceLinesModeled()).to_equal(10)
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


</details>
