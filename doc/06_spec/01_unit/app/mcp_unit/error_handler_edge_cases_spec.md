# Error Handler Edge Cases Specification

> <details>

<!-- sdn-diagram:id=error_handler_edge_cases_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=error_handler_edge_cases_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

error_handler_edge_cases_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=error_handler_edge_cases_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Handler Edge Cases Specification

## Scenarios

### Error Handler Edge Cases

### Tool Name Validation

#### detects at sign in tool name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("tool@name")
match result:
    case nil: fail("invalid tool name should be rejected")
    case err: expect(err.message.contains("invalid character")).to_equal(true)
```

</details>

#### detects exclamation mark in tool name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("tool!name")
match result:
    case nil: fail("invalid tool name should be rejected")
    case err: expect(err.message.contains("invalid character")).to_equal(true)
```

</details>

#### detects hash in tool name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("tool#name")
match result:
    case nil: fail("invalid tool name should be rejected")
    case err: expect(err.message.contains("invalid character")).to_equal(true)
```

</details>

#### detects dollar sign in tool name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("tool$name")
match result:
    case nil: fail("invalid tool name should be rejected")
    case err: expect(err.message.contains("invalid character")).to_equal(true)
```

</details>

#### detects percent in tool name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("tool%name")
match result:
    case nil: fail("invalid tool name should be rejected")
    case err: expect(err.message.contains("invalid character")).to_equal(true)
```

</details>

#### detects caret in tool name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("tool^name")
match result:
    case nil: fail("invalid tool name should be rejected")
    case err: expect(err.message.contains("invalid character")).to_equal(true)
```

</details>

#### detects ampersand in tool name

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("tool&name")
match result:
    case nil: fail("invalid tool name should be rejected")
    case err: expect(err.message.contains("invalid character")).to_equal(true)
```

</details>

#### accepts valid tool name with underscores

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("my_valid_tool")
expect(result).to_be_nil()
```

</details>

#### accepts valid tool name with hyphens

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("my-valid-tool")
expect(result).to_be_nil()
```

</details>

#### accepts valid tool name with slashes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("tools/list")
expect(result).to_be_nil()
```

</details>

### Error Category JSON-RPC Codes

#### maps ParseError to -32700

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ErrorCategory.ParseError.to_json_rpc_code()).to_equal(-32700)
```

</details>

#### maps InvalidRequest to -32600

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ErrorCategory.InvalidRequest.to_json_rpc_code()).to_equal(-32600)
```

</details>

#### maps MethodNotFound to -32601

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ErrorCategory.MethodNotFound.to_json_rpc_code()).to_equal(-32601)
```

</details>

#### maps InvalidParams to -32602

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ErrorCategory.InvalidParams.to_json_rpc_code()).to_equal(-32602)
```

</details>

#### maps InternalError to -32603

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ErrorCategory.InternalError.to_json_rpc_code()).to_equal(-32603)
```

</details>

### McpError Details and Recovery

#### creates error with details

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = mcp_error(ErrorCategory.Validation, "Bad input")
val detailed = err.with_details("Expected number, got string")
expect(detailed.details).to_equal("Expected number, got string")
expect(detailed.message).to_equal("Bad input")
```

</details>

#### marks error as unrecoverable

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = mcp_error(ErrorCategory.InternalError, "Fatal")
expect(err.recoverable).to_equal(true)
val fatal = err.as_unrecoverable()
expect(fatal.recoverable).to_equal(false)
```

</details>

#### converts to JSON-RPC with correct code

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = mcp_error(ErrorCategory.ParseError, "Bad JSON")
val json = err.to_json_rpc()
expect(json.contains("-32700")).to_equal(true)
expect(json.contains("Bad JSON")).to_equal(true)
```

</details>

### Validation Limits Comparison

#### default limits are more permissive than strict

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val default_limits = default_validation_limits()
val strict = strict_validation_limits()
expect(default_limits.max_content_length > strict.max_content_length).to_equal(true)
expect(default_limits.max_string_length > strict.max_string_length).to_equal(true)
```

</details>

#### strict limits enforce tighter bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val strict = strict_validation_limits()
expect(strict.max_content_length).to_equal(524288)
expect(strict.max_string_length).to_equal(32768)
expect(strict.max_uri_length).to_equal(1024)
expect(strict.max_tool_name_length).to_equal(128)
expect(strict.max_array_length).to_equal(500)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/error_handler_edge_cases_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Error Handler Edge Cases
- Tool Name Validation
- Error Category JSON-RPC Codes
- McpError Details and Recovery
- Validation Limits Comparison

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
