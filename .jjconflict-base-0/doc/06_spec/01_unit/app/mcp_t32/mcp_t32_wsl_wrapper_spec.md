# T32 MCP WSL Bridge & Wrapper Frontend Routing Specification

> Tests the logic encoded in the WSL bridge script (wsl_python3.sh) and the wrapper script frontend routing (bin/release/t32_mcp_server lines 176-246).

<!-- sdn-diagram:id=mcp_t32_wsl_wrapper_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_t32_wsl_wrapper_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_t32_wsl_wrapper_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_t32_wsl_wrapper_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 MCP WSL Bridge & Wrapper Frontend Routing Specification

Tests the logic encoded in the WSL bridge script (wsl_python3.sh) and the wrapper script frontend routing (bin/release/t32_mcp_server lines 176-246).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BUG-001, #BUG-006 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/app/mcp_t32/mcp_t32_wsl_wrapper_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the logic encoded in the WSL bridge script (wsl_python3.sh) and the
wrapper script frontend routing (bin/release/t32_mcp_server lines 176-246).

Since shell scripts cannot be directly executed from SPipe, this spec
re-implements the key decision logic as pure Simple functions and verifies
their correctness with unit tests.

## Key Concepts

| Concept | Description |
|---------|-------------|
| WSL detection | Checks /proc/version for "Microsoft" or "WSL" substring |
| TCP protocol | WSL forces NETTCP protocol for cross-boundary RCL |
| Host IP | Extracted from resolv.conf nameserver line |
| Frontend routing | T32_MCP_FRONTEND env var selects full (36 tools) or cold (13 tools) |

## Behavior

- WSL detection scans /proc/version for case-insensitive "Microsoft" or "WSL"
- TCP protocol is always NETTCP in WSL environments
- Host IP is parsed from "nameserver <IP>" lines in resolv.conf
- Frontend defaults to "full" mode (not "cold")
- Full mode routes to src/app/t32_mcp_server/main.spl (36 tools)
- Cold mode routes to examples/.../frontend_cold.spl (13 tools)

## Scenarios

### WSL detection and TCP config

#### WSL environment detection

#### detects WSL from proc version containing Microsoft

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proc_v = "Linux version 5.15.146.1-microsoft-standard-WSL2 (root@host) (gcc)"
expect(detect_wsl(proc_v)).to_equal(true)
```

</details>

#### detects WSL from proc version containing WSL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proc_v = "Linux version 5.15.0 (WSL custom build)"
expect(detect_wsl(proc_v)).to_equal(true)
```

</details>

#### detects WSL case-insensitively

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proc_v = "Linux version 5.15.0-MICROSOFT-custom"
expect(detect_wsl(proc_v)).to_equal(true)
```

</details>

#### non-WSL returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val proc_v = "Linux version 6.8.0-106-generic (buildd@lcy02-amd64-115)"
expect(detect_wsl(proc_v)).to_equal(false)
```

</details>

#### empty proc version returns false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(detect_wsl("")).to_equal(false)
```

</details>

#### TCP protocol config

#### WSL forces NETTCP protocol

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolve_protocol(true)).to_equal("NETTCP")
```

</details>

#### default protocol is NETTCP

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolve_protocol(false)).to_equal("NETTCP")
```

</details>

#### protocol string is exactly NETTCP

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val protocol = resolve_protocol(true)
expect(protocol).to_equal("NETTCP")
expect(protocol.len()).to_equal(6)
```

</details>

#### host IP resolution

#### resolves nameserver from resolv.conf format

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolv = "# This is auto-generated\nnameserver 172.28.160.1\nsearch localdomain"
expect(resolve_host_ip(resolv)).to_equal("172.28.160.1")
```

</details>

#### falls back to localhost when no nameserver

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val resolv = "# Empty resolv.conf\nsearch localdomain"
expect(resolve_host_ip(resolv)).to_equal("127.0.0.1")
```

</details>

#### parses nameserver line correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_nameserver("nameserver 10.0.0.1")).to_equal("10.0.0.1")
expect(parse_nameserver("nameserver 192.168.1.1")).to_equal("192.168.1.1")
```

</details>

#### ignores comment lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_nameserver("# nameserver 1.2.3.4")).to_equal("")
```

</details>

#### handles extra whitespace

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_nameserver("  nameserver  172.16.0.1  ")).to_equal("172.16.0.1")
```

</details>

#### returns empty for non-nameserver lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(parse_nameserver("search localdomain")).to_equal("")
expect(parse_nameserver("domain example.com")).to_equal("")
expect(parse_nameserver("")).to_equal("")
```

</details>

### wrapper frontend routing

#### frontend selection

#### default frontend is full

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolve_frontend("")).to_equal("full")
```

</details>

#### full frontend uses t32_mcp_server main.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/home/user/simple"
val artifact = resolve_source_artifact("full", root)
expect(artifact).to_equal("/home/user/simple/src/app/t32_mcp_server/main.spl")
```

</details>

#### cold frontend uses frontend_cold.spl

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/home/user/simple"
val artifact = resolve_source_artifact("cold", root)
expect(artifact).to_equal("/home/user/simple/examples/10_tooling/trace32_tools/t32_mcp/frontend_cold.spl")
```

</details>

#### env var overrides default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(resolve_frontend("cold")).to_equal("cold")
expect(resolve_frontend("full")).to_equal("full")
```

</details>

#### unknown frontend falls back to cold entrypoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/repo"
val artifact = resolve_source_artifact("unknown_value", root)
expect(artifact).to_contain("frontend_cold.spl")
```

</details>

#### full vs cold tool availability

#### full mode supports 36 tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(full_mode_tools().len()).to_equal(36)
```

</details>

#### cold mode supports 13 tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cold_mode_tools().len()).to_equal(13)
```

</details>

#### full mode includes session_open

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tools = full_mode_tools()
expect(tools.contains("t32_session_open")).to_equal(true)
```

</details>

#### full mode includes cmd_run

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tools = full_mode_tools()
expect(tools.contains("t32_cmd_run")).to_equal(true)
```

</details>

#### cold mode excludes session_open

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tools = cold_mode_tools()
expect(tools.contains("t32_session_open")).to_equal(false)
```

</details>

#### cold mode excludes cmd_run

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tools = cold_mode_tools()
expect(tools.contains("t32_cmd_run")).to_equal(false)
```

</details>

#### cold tools are a subset of full tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full = full_mode_tools()
val cold = cold_mode_tools()
var all_found = true
for tool in cold:
    if not full.contains(tool):
        all_found = false
expect(all_found).to_equal(true)
```

</details>

#### full mode includes window and screenshot tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tools = full_mode_tools()
expect(tools.contains("t32_window_capture")).to_equal(true)
expect(tools.contains("t32_screenshot")).to_equal(true)
expect(tools.contains("t32_window_snapshot")).to_equal(true)
```

</details>

#### cold mode includes dialog tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tools = cold_mode_tools()
expect(tools.contains("t32_dialog_parse")).to_equal(true)
expect(tools.contains("t32_dialog_get")).to_equal(true)
expect(tools.contains("t32_dialog_set")).to_equal(true)
expect(tools.contains("t32_dialog_click")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
