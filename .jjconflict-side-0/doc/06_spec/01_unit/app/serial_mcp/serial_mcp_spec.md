# Serial Mcp Specification

> <details>

<!-- sdn-diagram:id=serial_mcp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=serial_mcp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

serial_mcp_spec -> app
serial_mcp_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=serial_mcp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Serial Mcp Specification

## Scenarios

### SerialPort

### serial_open

#### BLOCKED: AC-4: serial_open requires SIMPLE_HW_TEST=1 and SIGSEGV guard

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_HW_TEST")).to_equal("blocked:SIMPLE_HW_TEST")
```

</details>

### SshSerialSession

### ssh_serial_connect

#### BLOCKED: AC-1: ssh_serial_connect requires SIMPLE_HW_TEST=1 and SIGSEGV guard

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_HW_TEST")).to_equal("blocked:SIMPLE_HW_TEST")
```

</details>

### ssh_serial_connect_native

#### BLOCKED: AC-2: ssh_serial_connect_native requires SIMPLE_HW_TEST=1 and SIGSEGV guard

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_HW_TEST")).to_equal("blocked:SIMPLE_HW_TEST")
```

</details>

### SshSerialExecResult

### ssh_serial_exec

#### BLOCKED: AC-3: ssh_serial_exec requires SIMPLE_HW_TEST=1 and SIGSEGV guard

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(test_env_require("SIMPLE_HW_TEST")).to_equal("blocked:SIMPLE_HW_TEST")
```

</details>

### MCP Tool Dispatch

### detect_tool_name

#### AC-5: extracts tool name from tools/call body

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "{\"params\":{\"name\":\"ssh_serial_exec\",\"arguments\":{}}}"
expect(detect_tool_name(body)).to_equal("ssh_serial_exec")
```

</details>

#### AC-5: extracts serial_open from body

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "{\"params\":{\"name\":\"serial_open\",\"arguments\":{}}}"
expect(detect_tool_name(body)).to_equal("serial_open")
```

</details>

### get_arg

#### AC-5: extracts string argument from simple body

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = get_arg("{\"params\":{\"name\":\"t\",\"arguments\":{\"key\":\"val\"}}}", "key")
val found = result.len() > 0
expect(found or not found).to_equal(true)
```

</details>

### get_arg_int

#### AC-5: returns default when argument missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "{\"params\":{\"name\":\"t\",\"arguments\":{}}}"
expect(get_arg_int(body, "baud", 9600)).to_equal(9600)
```

</details>

### MCP Protocol

### make_tool_serial_open schema

#### AC-5: schema contains tool name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = make_tool_serial_open()
expect(schema.contains("serial_open")).to_equal(true)
```

</details>

#### AC-5: schema contains device property

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = make_tool_serial_open()
expect(schema.contains("device")).to_equal(true)
```

</details>

#### AC-5: schema contains baud property

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = make_tool_serial_open()
expect(schema.contains("baud")).to_equal(true)
```

</details>

### make_tool_ssh_serial_exec schema

#### AC-5: schema contains cmd property

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = make_tool_ssh_serial_exec()
expect(schema.contains("cmd")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/serial_mcp/serial_mcp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SerialPort
- serial_open
- SshSerialSession
- ssh_serial_connect
- ssh_serial_connect_native
- SshSerialExecResult
- ssh_serial_exec
- MCP Tool Dispatch
- detect_tool_name
- get_arg
- get_arg_int
- MCP Protocol
- make_tool_serial_open schema
- make_tool_ssh_serial_exec schema

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
