# Transport Error Handling Specification

> <details>

<!-- sdn-diagram:id=transport_error_handling_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=transport_error_handling_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

transport_error_handling_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=transport_error_handling_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Transport Error Handling Specification

## Scenarios

### Transport Error Handling - Content-Length validation

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
    case nil: fail("negative Content-Length was accepted")
    case err: expect(err.message.contains("negative")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: accepts zero content length</summary>

#### accepts zero content length _(slow)_

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
    case nil: fail("excessive Content-Length was accepted")
    case err: expect(err.message.contains("exceeds")).to_equal(true)
```

</details>


</details>

### Transport Error Handling - JSON-RPC ID handling

<details>
<summary>Advanced: extracts integer ID from JSON</summary>

#### extracts integer ID from JSON _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo2(jp("id", "42"), jp("method", js("test")))
expect(extract_json_value(json, "id")).to_equal("42")
```

</details>


</details>

<details>
<summary>Advanced: handles null ID for notifications</summary>

#### handles null ID for notifications _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo1(jp("method", js("notifications/initialized")))
val id = extract_json_value(json, "id")
expect(id).to_equal("null")
```

</details>


</details>

<details>
<summary>Advanced: extracts method from request</summary>

#### extracts method from request _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo2(jp("id", "1"), jp("method", js("initialize")))
expect(extract_json_string(json, "method")).to_equal("initialize")
```

</details>


</details>

### Transport Error Handling - malformed JSON responses

<details>
<summary>Advanced: creates parse error response</summary>

#### creates parse error response _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("null", -32700, "Parse error")
expect(response.contains("-32700")).to_equal(true)
expect(response.contains("Parse error")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: creates invalid request response</summary>

#### creates invalid request response _(slow)_

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
<summary>Advanced: creates method not found response</summary>

#### creates method not found response _(slow)_

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
<summary>Advanced: creates invalid params response</summary>

#### creates invalid params response _(slow)_

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
<summary>Advanced: creates internal error response</summary>

#### creates internal error response _(slow)_

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

### Transport Error Handling - error categories

<details>
<summary>Advanced: parse error category</summary>

#### parse error category _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = mcp_error(ErrorCategory.ParseError, "Invalid JSON")
expect(err.category).to_equal(ErrorCategory.ParseError)
val json = err.to_json_rpc()
expect(json.contains("-32700")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: invalid request category</summary>

#### invalid request category _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = mcp_error(ErrorCategory.InvalidRequest, "Missing method")
expect(err.category).to_equal(ErrorCategory.InvalidRequest)
val json = err.to_json_rpc()
expect(json.contains("-32600")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: validation error category</summary>

#### validation error category _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = mcp_error(ErrorCategory.Validation, "Content too large")
expect(err.category).to_equal(ErrorCategory.Validation)
val json = err.to_json_rpc()
expect(json.contains("-32002")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: timeout error category</summary>

#### timeout error category _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = mcp_error(ErrorCategory.Timeout, "Request timed out")
expect(err.category).to_equal(ErrorCategory.Timeout)
```

</details>


</details>

### Transport Error Handling - character classification

<details>
<summary>Advanced: newline character in escape</summary>

#### newline character in escape _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val escaped = escape_json("line1{NL}line2")
expect(escaped.contains(NL)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: tab character in escape</summary>

#### tab character in escape _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val escaped = escape_json("col1\tcol2")
expect(escaped.contains("\t")).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: normal characters unchanged</summary>

#### normal characters unchanged _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json("hello")).to_equal("hello")
```

</details>


</details>

<details>
<summary>Advanced: empty string unchanged</summary>

#### empty string unchanged _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json("")).to_equal("")
```

</details>


</details>

### Transport Error Handling - logging for errors

<details>
<summary>Advanced: debug level for transport trace</summary>

#### debug level for transport trace _(slow)_

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
<summary>Advanced: warning level for malformed input</summary>

#### warning level for malformed input _(slow)_

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
<summary>Advanced: error level for transport failures</summary>

#### error level for transport failures _(slow)_

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
<summary>Advanced: critical level for unrecoverable errors</summary>

#### critical level for unrecoverable errors _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("critical")).to_equal(5)
```

</details>


</details>

### Transport Error Handling - error details

<details>
<summary>Advanced: attaches details to error</summary>

#### attaches details to error _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = mcp_error(ErrorCategory.ParseError, "Invalid JSON")
val detailed = err.with_details("Unexpected token at position 42")
expect(detailed.details).to_equal("Unexpected token at position 42")
```

</details>


</details>

<details>
<summary>Advanced: marks error as unrecoverable</summary>

#### marks error as unrecoverable _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = mcp_error(ErrorCategory.InternalError, "Fatal")
val fatal = err.as_unrecoverable()
expect(fatal.recoverable).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: default error is recoverable</summary>

#### default error is recoverable _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = mcp_error(ErrorCategory.ParseError, "Parse failed")
expect(err.recoverable).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/transport_error_handling_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Transport Error Handling - Content-Length validation
- Transport Error Handling - JSON-RPC ID handling
- Transport Error Handling - malformed JSON responses
- Transport Error Handling - error categories
- Transport Error Handling - character classification
- Transport Error Handling - logging for errors
- Transport Error Handling - error details

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 27 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
