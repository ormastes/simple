# MCP Command-Line Handshake

> System tests for every Simple-created local MCP command wrapper. Each scenario

<!-- sdn-diagram:id=mcp_cmdline_handshake_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_cmdline_handshake_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_cmdline_handshake_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_cmdline_handshake_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Command-Line Handshake

System tests for every Simple-created local MCP command wrapper. Each scenario

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/mcp_cmdline/mcp_cmdline_handshake_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

System tests for every Simple-created local MCP command wrapper. Each scenario
launches the server by command line, sends real MCP `initialize` and
`tools/list` frames over stdin, and requires a bounded response time.

## Scenarios

### MCP Command-Line Handshake

### REQ-MCP-CMD-001: local MCP wrappers answer real stdio handshakes

#### should launch simple_mcp_server and list Simple tools within the time limit

- Run bin/simple_mcp_server with initialize and tools/list frames
- expect probe ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run bin/simple_mcp_server with initialize and tools/list frames")
expect_probe_ok("simple_mcp", "bin/simple_mcp_server", "simple-mcp-full", "simple_status")
```

</details>

#### should launch simple_lsp_mcp_server and list LSP tools within the time limit

- Run bin/simple_lsp_mcp_server with initialize and tools/list frames
- expect probe ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run bin/simple_lsp_mcp_server with initialize and tools/list frames")
expect_probe_ok("simple_lsp_mcp", "bin/simple_lsp_mcp_server", "simple-lsp-mcp", "definition")
```

</details>

#### should fail closed when t32_mcp_server native artifact is missing

- Run bin/t32_mcp_server preflight without hosted fallback
- expect probe fails closed without native


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run bin/t32_mcp_server preflight without hosted fallback")
expect_probe_fails_closed_without_native("t32_mcp", "bin/t32_mcp_server")
```

</details>

#### should launch t32_lsp_mcp_server and list TRACE32 LSP tools within the time limit

- Run bin/t32_lsp_mcp_server with initialize and tools/list frames
- expect probe ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run bin/t32_lsp_mcp_server with initialize and tools/list frames")
expect_probe_ok("t32_lsp_mcp", "bin/t32_lsp_mcp_server", "simple-mcp-t32-lsp", "cmm_parse")
```

</details>

#### should launch obsidian_lsp_mcp_server and list Obsidian tools within the time limit

- Run bin/obsidian_lsp_mcp_server with initialize and tools/list frames
- expect probe ok


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run bin/obsidian_lsp_mcp_server with initialize and tools/list frames")
expect_probe_ok("obsidian_lsp_mcp", "bin/obsidian_lsp_mcp_server", "Obsidian LSP MCP Server", "obsidian")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
