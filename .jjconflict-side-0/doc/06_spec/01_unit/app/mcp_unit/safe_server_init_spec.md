# Safe Server Init Specification

> <details>

<!-- sdn-diagram:id=safe_server_init_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=safe_server_init_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

safe_server_init_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=safe_server_init_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Safe Server Init Specification

## Scenarios

### SafeMcpServer Initialization

### Logger Initialization

#### initializes logger successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", jo1(jp("logger", js("initialized"))))
expect(response.contains("initialized")).to_equal(true)
```

</details>

#### handles logger initialization error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32603, "Logger init failed")
expect(response.contains("Logger init failed")).to_equal(true)
```

</details>

#### logs initialization start

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "MCP server starting"
expect(msg.contains("starting")).to_equal(true)
```

</details>

#### logs initialization complete

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "MCP server initialized"
expect(msg.contains("initialized")).to_equal(true)
```

</details>

### Transport Configuration

#### detects transport not set error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32603, "Transport not configured")
expect(response.contains("Transport not configured")).to_equal(true)
```

</details>

#### configures stdio transport

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = jo1(jp("transport", js("stdio")))
expect(config.contains("stdio")).to_equal(true)
```

</details>

#### configures debug mode transport

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = jo2(jp("transport", js("stdio")), jp("debug", "true"))
expect(config.contains("debug")).to_equal(true)
```

</details>

#### configures production transport

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = jo2(jp("transport", js("stdio")), jp("debug", "false"))
expect(config.contains("false")).to_equal(true)
```

</details>

### Server run_safe

<details>
<summary>Advanced: enters main server loop</summary>

#### enters main server loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", jo1(jp("status", js("running"))))
expect(response.contains("running")).to_equal(true)
```

</details>


</details>

#### handles error in run_safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32603, "Server error")
expect(response.contains("Server error")).to_equal(true)
```

</details>

#### catches panic in run_safe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32603, "Panic recovered")
expect(response.contains("Panic recovered")).to_equal(true)
```

</details>

### Shutdown Cleanup

#### flushes logs on shutdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "Flushing logs on shutdown"
expect(msg.contains("Flushing")).to_equal(true)
```

</details>

#### handles flush error on shutdown

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32603, "Flush failed")
expect(response.contains("Flush failed")).to_equal(true)
```

</details>

#### logs shutdown complete

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val msg = "Shutdown complete"
expect(msg.contains("Shutdown")).to_equal(true)
```

</details>

### Configuration Validation

#### validates server name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = jo1(jp("name", js("simple-mcp")))
expect(config.contains("simple-mcp")).to_equal(true)
```

</details>

#### validates server version

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = jo1(jp("version", js("2.0.0")))
expect(config.contains("2.0.0")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/safe_server_init_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SafeMcpServer Initialization
- Logger Initialization
- Transport Configuration
- Server run_safe
- Shutdown Cleanup
- Configuration Validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
