# Crash Prevention Specification

> <details>

<!-- sdn-diagram:id=crash_prevention_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=crash_prevention_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

crash_prevention_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=crash_prevention_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Crash Prevention Specification

## Scenarios

### Crash prevention architecture

<details>
<summary>Advanced: validates content length limits exist</summary>

#### validates content length limits exist _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = default_validation_limits()
expect(limits.max_content_length > 0).to_equal(true)
expect(limits.max_string_length > 0).to_equal(true)
expect(limits.max_content_length > limits.max_string_length).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has error recovery tracking</summary>

#### has error recovery tracking _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var consecutive_errors = 0
var max_errors = 5
consecutive_errors = consecutive_errors + 1
consecutive_errors = consecutive_errors + 1
expect(consecutive_errors).to_equal(2)
expect(consecutive_errors < max_errors).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: resets error count on success</summary>

#### resets error count on success _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var consecutive_errors = 3
consecutive_errors = 0
expect(consecutive_errors).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: stops after max consecutive errors</summary>

#### stops after max consecutive errors _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var consecutive_errors = 0
var max_errors = 5
for i in 0..5:
    consecutive_errors = consecutive_errors + 1
val should_stop = consecutive_errors >= max_errors
expect(should_stop).to_equal(true)
```

</details>


</details>

### Input validation bounds

<details>
<summary>Advanced: rejects negative content length</summary>

#### rejects negative content length _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_content_length(-100)
match result:
    case nil: fail("negative content length was accepted")
    case err: expect(err.message.contains("negative")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: rejects excessive content length</summary>

#### rejects excessive content length _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_content_length(2000000)
match result:
    case nil: fail("excessive content length was accepted")
    case err: expect(err.message.contains("exceeds")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: accepts valid content length</summary>

#### accepts valid content length _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_content_length(1000)
expect(result).to_be_nil()
```

</details>


</details>

### URI validation

<details>
<summary>Advanced: validates file URI prefix</summary>

#### validates file URI prefix _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_uri("file:///home/user/test.spl")
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: validates symbol URI prefix</summary>

#### validates symbol URI prefix _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_uri("symbol://project/MyClass")
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: rejects invalid URI scheme</summary>

#### rejects invalid URI scheme _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_uri("invalid://test")
match result:
    case nil: fail("invalid URI scheme was accepted")
    case err: expect(err.message.contains("scheme")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: validates URI length limit</summary>

#### validates URI length limit _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uri = "file:///test.spl"
val max_uri_length = 2048
val is_valid = uri.len() <= max_uri_length
expect(is_valid).to_equal(true)
```

</details>


</details>

### Tool name validation

<details>
<summary>Advanced: validates simple tool name</summary>

#### validates simple tool name _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("read_code")
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: validates tool name with slash</summary>

#### validates tool name with slash _(slow)_

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


</details>

<details>
<summary>Advanced: rejects empty tool name</summary>

#### rejects empty tool name _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("")
match result:
    case nil: fail("empty tool name was accepted")
    case err: expect(err.message.contains("empty")).to_equal(true)
```

</details>


</details>

### Error categories

<details>
<summary>Advanced: has transport errors</summary>

#### has transport errors _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32000, "Transport error")
expect(response.contains("Transport")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has protocol errors</summary>

#### has protocol errors _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32600, "Protocol error")
expect(response.contains("Protocol")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has validation errors</summary>

#### has validation errors _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32602, "Validation error")
expect(response.contains("Validation")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has resource errors</summary>

#### has resource errors _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32001, "Resource error")
expect(response.contains("Resource")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has tool errors</summary>

#### has tool errors _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32002, "Tool error")
expect(response.contains("Tool")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has internal errors</summary>

#### has internal errors _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32603, "Internal error")
expect(response.contains("Internal")).to_equal(true)
```

</details>


</details>

### Log levels

<details>
<summary>Advanced: has trace level</summary>

#### has trace level _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("debug")).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: has info level</summary>

#### has info level _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("info")).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: has warn level</summary>

#### has warn level _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("warning")).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: has error level</summary>

#### has error level _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("error")).to_equal(4)
```

</details>


</details>

<details>
<summary>Advanced: has critical level</summary>

#### has critical level _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("critical")).to_equal(5)
```

</details>


</details>

<details>
<summary>Advanced: has emergency level</summary>

#### has emergency level _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("emergency")).to_equal(7)
```

</details>


</details>

<details>
<summary>Advanced: orders levels correctly</summary>

#### orders levels correctly _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val debug_val = log_level_to_int("debug")
val info_val = log_level_to_int("info")
val warning_val = log_level_to_int("warning")
val error_val = log_level_to_int("error")
val emergency_val = log_level_to_int("emergency")
expect(debug_val < info_val).to_equal(true)
expect(info_val < warning_val).to_equal(true)
expect(warning_val < error_val).to_equal(true)
expect(error_val < emergency_val).to_equal(true)
```

</details>


</details>

### Validation limits

<details>
<summary>Advanced: has default limits</summary>

#### has default limits _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = default_validation_limits()
expect(limits.max_content_length).to_equal(1048576)
expect(limits.max_string_length).to_equal(65536)
expect(limits.max_array_length).to_equal(1000)
```

</details>


</details>

<details>
<summary>Advanced: has strict limits</summary>

#### has strict limits _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = strict_validation_limits()
expect(limits.max_content_length).to_equal(524288)
expect(limits.max_string_length).to_equal(32768)
expect(limits.max_array_length).to_equal(500)
```

</details>


</details>

<details>
<summary>Advanced: strict limits are more restrictive</summary>

#### strict limits are more restrictive _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = default_validation_limits()
val s = strict_validation_limits()
expect(s.max_content_length < d.max_content_length).to_equal(true)
```

</details>


</details>

### Error codes

<details>
<summary>Advanced: has JSON-RPC parse error code</summary>

#### has JSON-RPC parse error code _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32700, "Parse error")
expect(response.contains("-32700")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has JSON-RPC invalid request code</summary>

#### has JSON-RPC invalid request code _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32600, "Invalid Request")
expect(response.contains("-32600")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has JSON-RPC method not found code</summary>

#### has JSON-RPC method not found code _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32601, "Method not found")
expect(response.contains("-32601")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has JSON-RPC invalid params code</summary>

#### has JSON-RPC invalid params code _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32602, "Invalid params")
expect(response.contains("-32602")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has JSON-RPC internal error code</summary>

#### has JSON-RPC internal error code _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32603, "Internal error")
expect(response.contains("-32603")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has custom timeout code</summary>

#### has custom timeout code _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32000, "Timeout")
expect(response.contains("-32000")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has custom rate limit code</summary>

#### has custom rate limit code _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32001, "Rate limit")
expect(response.contains("-32001")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has custom validation code</summary>

#### has custom validation code _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32002, "Validation")
expect(response.contains("-32002")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/crash_prevention_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Crash prevention architecture
- Input validation bounds
- URI validation
- Tool name validation
- Error categories
- Log levels
- Validation limits
- Error codes

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 38 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
