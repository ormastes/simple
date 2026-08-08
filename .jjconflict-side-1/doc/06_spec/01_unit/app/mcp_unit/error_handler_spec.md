# Error Handler Specification

> <details>

<!-- sdn-diagram:id=error_handler_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=error_handler_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

error_handler_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=error_handler_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Handler Specification

## Scenarios

### ErrorCategory

<details>
<summary>Advanced: converts to string correctly</summary>

#### converts to string correctly _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ErrorCategory.ParseError.to_string()).to_equal("parse_error")
expect(ErrorCategory.InvalidRequest.to_string()).to_equal("invalid_request")
expect(ErrorCategory.MethodNotFound.to_string()).to_equal("method_not_found")
expect(ErrorCategory.InvalidParams.to_string()).to_equal("invalid_params")
expect(ErrorCategory.InternalError.to_string()).to_equal("internal_error")
expect(ErrorCategory.Timeout.to_string()).to_equal("timeout")
```

</details>


</details>

### McpError

<details>
<summary>Advanced: creates error with category and message</summary>

#### creates error with category and message _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = mcp_error(ErrorCategory.InvalidRequest, "Bad request")
expect(err.category).to_equal(ErrorCategory.InvalidRequest)
expect(err.message).to_equal("Bad request")
expect(err.recoverable).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: can be marked as unrecoverable</summary>

#### can be marked as unrecoverable _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = mcp_error(ErrorCategory.InternalError, "Fatal error")
val unrecoverable = err.as_unrecoverable()
expect(unrecoverable.recoverable).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: can have details attached</summary>

#### can have details attached _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = mcp_error(ErrorCategory.Validation, "Invalid input")
val with_details = err.with_details("Expected number, got string")
expect(with_details.details).to_equal("Expected number, got string")
```

</details>


</details>

<details>
<summary>Advanced: converts to JSON-RPC error</summary>

#### converts to JSON-RPC error _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = mcp_error(ErrorCategory.MethodNotFound, "Unknown method")
val json = err.to_json_rpc()
expect(json.contains("-32601")).to_equal(true)
expect(json.contains("Unknown method")).to_equal(true)
```

</details>


</details>

### ValidationLimits

<details>
<summary>Advanced: creates default limits</summary>

#### creates default limits _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = default_validation_limits()
expect(limits.max_content_length).to_equal(1048576)
expect(limits.max_string_length).to_equal(65536)
```

</details>


</details>

<details>
<summary>Advanced: creates strict limits</summary>

#### creates strict limits _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val limits = strict_validation_limits()
expect(limits.max_content_length).to_equal(524288)
expect(limits.max_string_length).to_equal(32768)
```

</details>


</details>

### InputValidator - content length

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

<details>
<summary>Advanced: accepts zero length</summary>

#### accepts zero length _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_content_length(0)
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: rejects negative content length</summary>

#### rejects negative content length _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_content_length(-1)
match result:
    case nil: fail("negative content length should be rejected")
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
    case nil: fail("excessive content length should be rejected")
    case err: expect(err.message.contains("exceeds")).to_equal(true)
```

</details>


</details>

### InputValidator - string validation

<details>
<summary>Advanced: accepts valid string</summary>

#### accepts valid string _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_string("hello world")
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: accepts empty string</summary>

#### accepts empty string _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_string("")
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: rejects excessive string length</summary>

#### rejects excessive string length _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var long_string = ""
var i = 0
while i < 70000:
    long_string = long_string + "x"
    i = i + 1

val validator = input_validator()
val result = validator.validate_string(long_string)
match result:
    case nil: expect(long_string.len()).to_be_greater_than(65536)
    case err: expect(err.message.contains("exceeds")).to_equal(true)
```

</details>


</details>

### InputValidator - URI validation

<details>
<summary>Advanced: accepts valid file URI</summary>

#### accepts valid file URI _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_uri("file:///path/to/file.txt")
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: accepts valid symbol URI</summary>

#### accepts valid symbol URI _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_uri("symbol://MyClass.method")
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: accepts valid project URI</summary>

#### accepts valid project URI _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_uri("project://myproject")
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: accepts valid http URI</summary>

#### accepts valid http URI _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_uri("http://example.com")
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: accepts valid https URI</summary>

#### accepts valid https URI _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_uri("https://example.com/path")
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: rejects empty URI</summary>

#### rejects empty URI _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_uri("")
match result:
    case nil: fail("empty URI should be rejected")
    case err: expect(err.message.contains("empty")).to_equal(true)
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
val result = validator.validate_uri("ftp://example.com")
match result:
    case nil: fail("invalid URI scheme should be rejected")
    case err: expect(err.message.contains("scheme")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: rejects excessive URI length</summary>

#### rejects excessive URI length _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var long_uri = "file://"
var i = 0
while i < 3000:
    long_uri = long_uri + "x"
    i = i + 1

val validator = input_validator()
val result = validator.validate_uri(long_uri)
match result:
    case nil: expect(long_uri.len()).to_be_greater_than(2048)
    case err: expect(err.message.contains("exceeds")).to_equal(true)
```

</details>


</details>

### InputValidator - tool name validation

<details>
<summary>Advanced: accepts valid tool name</summary>

#### accepts valid tool name _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("my_tool")
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: accepts tool name with slashes</summary>

#### accepts tool name with slashes _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("category/tool_name")
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: accepts tool name with hyphens</summary>

#### accepts tool name with hyphens _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("my-tool-name")
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
    case nil: fail("empty tool name should be rejected")
    case err: expect(err.message.contains("empty")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: rejects tool name with invalid characters</summary>

#### rejects tool name with invalid characters _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_tool_name("tool@name")
match result:
    case nil: fail("tool names with invalid characters should be rejected")
    case err: expect(err.message.contains("invalid character")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: rejects excessive tool name length</summary>

#### rejects excessive tool name length _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var long_name = ""
var i = 0
while i < 300:
    long_name = long_name + "x"
    i = i + 1

val validator = input_validator()
val result = validator.validate_tool_name(long_name)
match result:
    case nil: expect(long_name.len()).to_be_greater_than(255)
    case err: expect(err.category).to_equal(ErrorCategory.Validation)
```

</details>


</details>

### InputValidator - array validation

<details>
<summary>Advanced: accepts valid array length</summary>

#### accepts valid array length _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_array_length(100)
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: accepts zero array length</summary>

#### accepts zero array length _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_array_length(0)
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: rejects negative array length</summary>

#### rejects negative array length _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_array_length(-1)
match result:
    case nil: fail("negative array length should be rejected")
    case err: expect(err.message.contains("negative")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: rejects excessive array length</summary>

#### rejects excessive array length _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_array_length(2000)
match result:
    case nil: fail("excessive array length should be rejected")
    case err: expect(err.message.contains("exceeds")).to_equal(true)
```

</details>


</details>

### InputValidator - parameter validation

<details>
<summary>Advanced: validates all parameters</summary>

#### validates all parameters _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
var params = {}
params["key1"] = "value1"
params["key2"] = "value2"
val result = validator.validate_params(params)
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: rejects params with excessively long values</summary>

#### rejects params with excessively long values _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
var long_value = ""
var i = 0
while i < 70000:
    long_value = long_value + "x"
    i = i + 1

var params = {}
params["key"] = long_value
val result = validator.validate_params(params)
match result:
    case nil: expect(long_value.len()).to_be_greater_than(65536)
    case err: expect(err.category).to_equal(ErrorCategory.Validation)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/error_handler_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ErrorCategory
- McpError
- ValidationLimits
- InputValidator - content length
- InputValidator - string validation
- InputValidator - URI validation
- InputValidator - tool name validation
- InputValidator - array validation
- InputValidator - parameter validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 34 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
