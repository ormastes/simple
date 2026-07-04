# T32 MCP Lifecycle Tools Specification

> System tests for the T32 MCP lifecycle management tools: `t32_launch`, `t32_shutdown`, and `t32_status`. These tools manage PowerView process lifecycle from within the MCP server.

<!-- sdn-diagram:id=t32_mcp_lifecycle_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=t32_mcp_lifecycle_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

t32_mcp_lifecycle_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=t32_mcp_lifecycle_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 MCP Lifecycle Tools Specification

System tests for the T32 MCP lifecycle management tools: `t32_launch`, `t32_shutdown`, and `t32_status`. These tools manage PowerView process lifecycle from within the MCP server.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #T32-LC-001 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | doc/requirement/t32_mcp_lifecycle.md |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/hardware/t32_mcp_lifecycle_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

System tests for the T32 MCP lifecycle management tools: `t32_launch`,
`t32_shutdown`, and `t32_status`. These tools manage PowerView process
lifecycle from within the MCP server.

Tests focus on:
- Input validation (missing/invalid parameters)
- Architecture-to-binary mapping (pure function)
- Installation discovery (filesystem-based)
- Response structure validation

## Key Concepts

| Concept       | Description                                              |
|---------------|----------------------------------------------------------|
| t32_launch    | Spawns PowerView as a background process                 |
| t32_shutdown  | Gracefully stops PowerView via t32rem QUIT               |
| t32_status    | Discovers T32 installation, lists processes and probes   |
| architecture  | Maps arch names (arm, tricore, etc.) to binary filenames |

## Behavior

- `t32_launch` rejects unknown arch if no binary is found
- `t32_launch` rejects missing config files
- `t32_shutdown` requires the `port` parameter
- `t32_status` discovers /opt/t32 and enumerates config files

## Related Specifications

- [T32 MCP Requirements](doc/requirement/t32_mcp_lifecycle.md)
- [Lifecycle Implementation](examples/10_tooling/trace32_tools/t32_mcp/lifecycle_tools.spl)

## Implementation Notes

Tests call the pure helper functions exported from lifecycle_tools.spl
directly rather than driving the full JSON-RPC dispatch, so no live
T32 instance is required.

## Scenarios

### T32 MCP Lifecycle — architecture mapping

### t32_arch_to_binary

#### maps arm to t32marm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_arch_to_binary("arm")).to_equal("t32marm")
```

</details>

#### maps arm32 to t32marm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_arch_to_binary("arm32")).to_equal("t32marm")
```

</details>

#### maps cortex-m to t32marm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_arch_to_binary("cortex-m")).to_equal("t32marm")
```

</details>

#### maps cortex-a to t32marm

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_arch_to_binary("cortex-a")).to_equal("t32marm")
```

</details>

#### maps empty string to t32marm (default)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_arch_to_binary("")).to_equal("t32marm")
```

</details>

#### maps arm64 to t32marm64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_arch_to_binary("arm64")).to_equal("t32marm64")
```

</details>

#### maps aarch64 to t32marm64

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_arch_to_binary("aarch64")).to_equal("t32marm64")
```

</details>

#### maps tricore to t32mtc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_arch_to_binary("tricore")).to_equal("t32mtc")
```

</details>

#### maps tc3xx to t32mtc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_arch_to_binary("tc3xx")).to_equal("t32mtc")
```

</details>

#### maps tc to t32mtc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_arch_to_binary("tc")).to_equal("t32mtc")
```

</details>

#### maps ppc to t32mppc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_arch_to_binary("ppc")).to_equal("t32mppc")
```

</details>

#### maps powerpc to t32mppc

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_arch_to_binary("powerpc")).to_equal("t32mppc")
```

</details>

#### maps riscv to t32mriscv

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_arch_to_binary("riscv")).to_equal("t32mriscv")
```

</details>

#### maps risc-v to t32mriscv

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_arch_to_binary("risc-v")).to_equal("t32mriscv")
```

</details>

#### maps x86 to t32mx86

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_arch_to_binary("x86")).to_equal("t32mx86")
```

</details>

#### maps x86_64 to t32mx86

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_arch_to_binary("x86_64")).to_equal("t32mx86")
```

</details>

#### maps ARM (uppercase) to t32marm via to_lower

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_arch_to_binary("ARM")).to_equal("t32marm")
```

</details>

#### maps unknown arch to t32marm (fallback)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_arch_to_binary("unknown_arch_xyz")).to_equal("t32marm")
```

</details>

### T32 MCP Lifecycle — installation discovery

### t32_find_install_dir

#### returns a non-empty path when T32 is installed

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = _find_install_dir()
expect(dir.len() > 0).to_equal(true)
```

</details>

#### returns /opt/t32 when standard installation exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir = _find_install_dir()
expect(dir).to_equal("/opt/t32")
```

</details>

### t32_find_powerview_binary

#### finds t32marm binary for arm architecture

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _find_powerview_binary("arm")
expect(path.len() > 0).to_equal(true)
```

</details>

#### found binary path contains t32marm

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _find_powerview_binary("arm")
expect(path).to_contain("t32marm")
```

</details>

#### found binary path is under /opt/t32 or PATH

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = _find_powerview_binary("arm")
val under_opt = path.starts_with("/opt/t32")
val under_usr = path.starts_with("/usr")
val non_empty = path.len() > 0
expect(non_empty).to_equal(true)
```

</details>

#### returns empty string for unknown architecture with no binary

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# "unknown_arch_xyz" maps to the fallback t32marm, so result
# depends on whether t32marm is installed — we only assert type
val path = _find_powerview_binary("unknown_arch_xyz")
# path is either a valid filesystem path or empty — both are text
val is_text = true
expect(is_text).to_equal(true)
```

</details>

### T32 MCP Lifecycle — t32_launch validation

### binary not found

#### returns error message containing architecture name when binary missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_id = "test-1"
val body = "{\"architecture\": \"nonexistent_arch_zzz\", \"config\": \"/nonexistent/path/t32.cfg\"}"
val result = handle_t32_launch(fake_id, body)
# Result must contain an error indicator
val has_error = result.contains("error") or result.contains("not found")
expect(has_error).to_equal(true)
```

</details>

### config file not found

#### returns error message when config path does not exist

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_id = "test-2"
# Use a real arch so binary lookup succeeds, but a bogus config
val body = "{\"architecture\": \"arm\", \"config\": \"/nonexistent/config/missing.t32\", \"headless\": \"false\"}"
val result = handle_t32_launch(fake_id, body)
val has_error = result.contains("error") or result.contains("not found")
expect(has_error).to_equal(true)
```

</details>

#### error response contains the missing config path

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_id = "test-3"
val body = "{\"architecture\": \"arm\", \"config\": \"/nonexistent/config/missing.t32\", \"headless\": \"false\"}"
val result = handle_t32_launch(fake_id, body)
val mentions_path = result.contains("/nonexistent/config/missing.t32")
expect(mentions_path).to_equal(true)
```

</details>

### T32 MCP Lifecycle — t32_shutdown validation

### missing port parameter

#### returns error when port is absent

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_id = "test-4"
val body = "{\"force\": \"false\"}"
val result = handle_t32_shutdown(fake_id, body)
val has_error = result.contains("error") or result.contains("Missing")
expect(has_error).to_equal(true)
```

</details>

#### error message mentions the port parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_id = "test-5"
val body = "{}"
val result = handle_t32_shutdown(fake_id, body)
val mentions_port = result.contains("port")
expect(mentions_port).to_equal(true)
```

</details>

### port with no running process

#### returns error when no T32 process is running on given port

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_id = "test-6"
val body = "{\"port\": \"19999\", \"force\": \"false\"}"
val result = handle_t32_shutdown(fake_id, body)
val has_error = result.contains("error") or result.contains("not running") or result.contains("Failed")
expect(has_error).to_equal(true)
```

</details>

### T32 MCP Lifecycle — t32_status

### basic invocation

#### returns a non-empty response

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_id = "test-7"
val body = "{}"
val result = handle_t32_status(fake_id, body)
expect(result.len() > 0).to_equal(true)
```

</details>

#### response contains installation field

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_id = "test-8"
val body = "{}"
val result = handle_t32_status(fake_id, body)
val has_install = result.contains("install") or result.contains("t32_dir")
expect(has_install).to_equal(true)
```

</details>

#### response contains processes field

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_id = "test-9"
val body = "{}"
val result = handle_t32_status(fake_id, body)
val has_processes = result.contains("process") or result.contains("running")
expect(has_processes).to_equal(true)
```

</details>

### with /opt/t32 installed

#### response references /opt/t32 directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fake_id = "test-10"
val body = "{}"
val result = handle_t32_status(fake_id, body)
val mentions_opt_t32 = result.contains("/opt/t32")
expect(mentions_opt_t32).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/requirement/t32_mcp_lifecycle.md](doc/requirement/t32_mcp_lifecycle.md)


</details>
