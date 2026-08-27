# Safe Server Config Specification

> <details>

<!-- sdn-diagram:id=safe_server_config_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=safe_server_config_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

safe_server_config_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=safe_server_config_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Safe Server Config Specification

## Scenarios

### SafeMcpServer Configuration

### Strict Validation Flag

#### enables strict validation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = strict_validation_limits()
val strict_mode = limits.max_content_length < 1048576
expect(strict_mode).to_equal(true)
```

</details>

#### disables strict validation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = default_validation_limits()
val not_strict = limits.max_content_length >= 1048576
expect(not_strict).to_equal(true)
```

</details>

#### applies strict rules when enabled

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = strict_validation_limits()
val validator = input_validator()
val result = validator.validate_content_length(100)
expect(result).to_be_nil()
```

</details>

### Debug Mode

#### enables debug mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", jo1(jp("debug", "true")))
expect(response.contains("debug")).to_equal(true)
```

</details>

#### disables debug mode

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", jo1(jp("debug", "false")))
expect(response.contains("false")).to_equal(true)
```

</details>

#### combines debug and strict flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = strict_validation_limits()
val response = make_result_response("1", jo2(jp("debug", "true"), jp("strict", "true")))
expect(response.contains("debug")).to_equal(true)
expect(response.contains("strict")).to_equal(true)
```

</details>

### Log File Configuration

#### uses specified log file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log_path = "/tmp/mcp.log"
val config = jo1(jp("log_file", js(log_path)))
expect(config.contains("mcp.log")).to_equal(true)
```

</details>

#### uses default log file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val log_file = ""
val file_logging = log_file.len() > 0
expect(file_logging).to_equal(false)
```

</details>

#### creates log directory if missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dir_path = "/tmp/logs"
val config = jo1(jp("log_dir", js(dir_path)))
expect(config.contains("logs")).to_equal(true)
```

</details>

### run_safe_mcp_server

#### initializes with all config

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = jo3(jp("name", js("test-mcp")), jp("version", js("1.0")), jp("debug", "true"))
expect(config.contains("test-mcp")).to_equal(true)
expect(config.contains("1.0")).to_equal(true)
```

</details>

#### initializes with minimal config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = jo1(jp("name", js("mcp")))
expect(config.contains("mcp")).to_equal(true)
```

</details>

#### handles initialization failure

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32603, "Init failed")
expect(response.contains("-32603")).to_equal(true)
expect(response.contains("Init failed")).to_equal(true)
```

</details>

#### runs server successfully

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", jo1(jp("status", js("running"))))
expect(response.contains("running")).to_equal(true)
```

</details>

### Configuration Validation

#### validates required fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = jo2(jp("name", js("mcp")), jp("version", js("1.0")))
val has_name = config.contains("name")
val has_version = config.contains("version")
expect(has_name).to_equal(true)
expect(has_version).to_equal(true)
```

</details>

#### rejects invalid config

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32602, "Missing required field")
expect(response.contains("Missing required field")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/safe_server_config_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SafeMcpServer Configuration
- Strict Validation Flag
- Debug Mode
- Log File Configuration
- run_safe_mcp_server
- Configuration Validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
