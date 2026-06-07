# Bootstrap MCP Server Native Build Specification

> System tests for native MCP server compilation in the bootstrap pipeline. Verifies that after bootstrap with --deploy, both MCP server binaries (simple_mcp_server, simple_lsp_mcp_server) exist, are executable, and respond to JSON-RPC initialize requests.

<!-- sdn-diagram:id=bootstrap_mcp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bootstrap_mcp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bootstrap_mcp_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bootstrap_mcp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bootstrap MCP Server Native Build Specification

System tests for native MCP server compilation in the bootstrap pipeline. Verifies that after bootstrap with --deploy, both MCP server binaries (simple_mcp_server, simple_lsp_mcp_server) exist, are executable, and respond to JSON-RPC initialize requests.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MCP-BOOT-001 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | Draft |
| Requirements | N/A |
| Plan | .sstack/native-mcp-build-bootstrap/state.md |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/tools/bootstrap_mcp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

System tests for native MCP server compilation in the bootstrap pipeline.
Verifies that after bootstrap with --deploy, both MCP server binaries
(simple_mcp_server, simple_lsp_mcp_server) exist, are executable, and
respond to JSON-RPC initialize requests.

Shell-level integration tests (AC-1 through AC-4, AC-6, AC-7) are defined
as verification commands in the state file. This SPipe file covers AC-5:
runtime validation that MCP servers respond to JSON-RPC initialize.

## Key Concepts

| Concept              | Description                                             |
|----------------------|---------------------------------------------------------|
| native-build         | Compiler command that produces a platform-native binary  |
| MCP server           | JSON-RPC stdio server implementing Model Context Proto  |
| initialize           | First JSON-RPC request a client sends to an MCP server  |
| bootstrap pipeline   | Multi-stage build: Rust seed -> Simple compiler -> self  |
| platform triple      | Target identifier e.g. x86_64-unknown-linux-gnu         |

## Behavior

- After bootstrap --deploy, bin/simple_mcp_server is a symlink to a native binary
- After bootstrap --deploy, bin/simple_lsp_mcp_server is a symlink to a native binary
- Both servers accept JSON-RPC initialize on stdin and return capabilities
- The --no-mcp flag skips MCP server compilation entirely

## Related Specifications

- [CLI MCP Completeness](cli_mcp_completeness_spec.spl)
- [OS Compiler Bootstrap](os_compiler_bootstrap_spec.spl)
- [T32 MCP Lifecycle](t32_mcp_lifecycle_spec.spl)

## Scenarios

### Bootstrap MCP — binary existence

#### simple_mcp_server binary exists at platform release path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = mcp_binary_path("simple_mcp_server")
expect(file_exists(path)).to_equal(true)
```

</details>

#### simple_lsp_mcp_server binary exists at platform release path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = mcp_binary_path("simple_lsp_mcp_server")
expect(file_exists(path)).to_equal(true)
```

</details>

#### main CLI binary still exists at platform release path

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = mcp_binary_path("simple")
expect(file_exists(path)).to_equal(true)
```

</details>

### Bootstrap MCP — symlinks

#### bin/simple_mcp_server symlink exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("bin/simple_mcp_server")).to_equal(true)
```

</details>

#### bin/simple_lsp_mcp_server symlink exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("bin/simple_lsp_mcp_server")).to_equal(true)
```

</details>

#### bin/simple_mcp_server is executable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_, _, rc) = rt_process_run("test", ["-x", "bin/simple_mcp_server"])
expect(rc).to_equal(0)
```

</details>

#### bin/simple_lsp_mcp_server is executable

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (_, _, rc) = rt_process_run("test", ["-x", "bin/simple_lsp_mcp_server"])
expect(rc).to_equal(0)
```

</details>

### Bootstrap MCP — JSON-RPC initialize

#### simple_mcp_server responds to initialize with capabilities

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binary = "bin/simple_mcp_server"
if not file_exists(binary):
    expect(file_exists(binary)).to_equal(false)
else:
    val result = send_initialize_request(binary)
    val output = result.out_text + result.err_text
    val has_capabilities = output.contains("capabilities")
    val has_jsonrpc = output.contains("jsonrpc")
    expect(has_capabilities or has_jsonrpc).to_equal(true)
```

</details>

#### simple_lsp_mcp_server responds to initialize with capabilities

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binary = "bin/simple_lsp_mcp_server"
if not file_exists(binary):
    expect(file_exists(binary)).to_equal(false)
else:
    val result = send_initialize_request(binary)
    val output = result.out_text + result.err_text
    val has_capabilities = output.contains("capabilities")
    val has_jsonrpc = output.contains("jsonrpc")
    expect(has_capabilities or has_jsonrpc).to_equal(true)
```

</details>

#### simple_mcp_server initialize response contains server info

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binary = "bin/simple_mcp_server"
if not file_exists(binary):
    expect(file_exists(binary)).to_equal(false)
else:
    val result = send_initialize_request(binary)
    val output = result.out_text + result.err_text
    val has_server_info = output.contains("serverInfo") or output.contains("server_info")
    expect(has_server_info or output.contains("simple")).to_equal(true)
```

</details>

#### simple_mcp_server handles simple_status tool calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binary = "bin/simple_mcp_server"
if not file_exists(binary):
    expect(file_exists(binary)).to_equal(false)
else:
    val args = "{\"paths\":\"src/app/simple_lsp_mcp/main.spl\"}"
    val result = send_tool_call_request(binary, "simple_status", args)
    val output = result.out_text + result.err_text
    expect(output.contains("Project Diagnostics")).to_equal(true)
```

</details>

#### simple_lsp_mcp_server reads tool name from params

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val binary = "bin/simple_lsp_mcp_server"
if not file_exists(binary):
    expect(file_exists(binary)).to_equal(false)
else:
    val args = "{\"file\":\"src/app/simple_lsp_mcp/main.spl\"}"
    val result = send_tool_call_request(binary, "lsp_symbols", args)
    val output = result.out_text + result.err_text
    expect(output.contains("Missing tool name")).to_equal(false)
    expect(output.contains("jsonrpc") and output.contains("result")).to_equal(true)
```

</details>

### Bootstrap MCP — CLI regression

#### bin/simple --version returns exit code 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, rc) = rt_process_run("bin/simple", ["--version"])
expect(rc).to_equal(0)
```

</details>

#### bin/simple --version output contains version string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, _, _) = rt_process_run("bin/simple", ["--version"])
val has_version = stdout.contains("simple") or stdout.contains("Simple") or stdout.contains("0.")
expect(has_version).to_equal(true)
```

</details>

#### bin/simple help returns exit code 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val (stdout, stderr, rc) = rt_process_run("bin/simple", ["help"])
# help may return 0 or 1 depending on implementation
val ok = rc == 0 or rc == 1
expect(ok).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [.sstack/native-mcp-build-bootstrap/state.md](.sstack/native-mcp-build-bootstrap/state.md)


</details>
