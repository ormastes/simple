# Transport Tcp Specification

> <details>

<!-- sdn-diagram:id=transport_tcp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=transport_tcp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

transport_tcp_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=transport_tcp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Transport Tcp Specification

## Scenarios

### TCP Transport - message building

<details>
<summary>Advanced: builds valid JSON-RPC request</summary>

#### builds valid JSON-RPC request _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val request = jo3(jp("jsonrpc", js("2.0")), jp("id", "1"), jp("method", js("test")))
expect(request.contains("jsonrpc")).to_equal(true)
expect(request.contains("2.0")).to_equal(true)
expect(request.contains("test")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds request with params</summary>

#### builds request with params _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = jo1(jp("path", js("/test.spl")))
val request = jo3(jp("jsonrpc", js("2.0")), jp("id", "1"), jp("method", js("tools/call")))
expect(request.contains("tools/call")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds notification without id</summary>

#### builds notification without id _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_notification("notifications/initialized", LB() + RB())
expect(notif.contains("notifications/initialized")).to_equal(true)
expect(notif.contains("jsonrpc")).to_equal(true)
```

</details>


</details>

### TCP Transport - response formatting

<details>
<summary>Advanced: formats result response</summary>

#### formats result response _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", jo1(jp("status", js("ok"))))
expect(response.contains("jsonrpc")).to_equal(true)
expect(response.contains("result")).to_equal(true)
expect(response.contains("ok")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: formats error response</summary>

#### formats error response _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32600, "Invalid request")
expect(response.contains("error")).to_equal(true)
expect(response.contains("-32600")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: includes id in response</summary>

#### includes id in response _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("42", js("done"))
expect(response.contains("42")).to_equal(true)
```

</details>


</details>

### TCP Transport - Content-Length framing

<details>
<summary>Advanced: calculates content length for response</summary>

#### calculates content length for response _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", js("ok"))
val content_length = response.len()
expect(content_length > 0).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds Content-Length header</summary>

#### builds Content-Length header _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", js("ok"))
val header = "Content-Length: " + response.len().to_string() + "\r{NL}\r{NL}"
expect(header.starts_with("Content-Length:")).to_equal(true)
expect(header.ends_with("\r{NL}\r{NL}")).to_equal(true)
```

</details>


</details>

### TCP Transport - read operations

<details>
<summary>Advanced: extracts method from received message</summary>

#### extracts method from received message _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = jo2(jp("method", js("initialize")), jp("id", "1"))
expect(extract_json_string(json, "method")).to_equal("initialize")
```

</details>


</details>

<details>
<summary>Advanced: extracts id from received message</summary>

#### extracts id from received message _(slow)_

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
<summary>Advanced: extracts params from received message</summary>

#### extracts params from received message _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = jo1(jp("name", js("read_code")))
val json = jo2(jp("method", js("tools/call")), jp("params", params))
expect(extract_json_string(json, "method")).to_equal("tools/call")
```

</details>


</details>

### TCP Transport - write operations

<details>
<summary>Advanced: writes result response</summary>

#### writes result response _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", jo1(jp("data", js("hello"))))
expect(response.contains("result")).to_equal(true)
expect(response.contains("hello")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: writes error response</summary>

#### writes error response _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_error_response("1", -32603, "Internal error")
expect(response.contains("error")).to_equal(true)
expect(response.contains("-32603")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: writes notification</summary>

#### writes notification _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val notif = make_notification_no_params("notifications/tools/list_changed")
expect(notif.contains("tools/list_changed")).to_equal(true)
```

</details>


</details>

### TCP Transport - connection validation

<details>
<summary>Advanced: validates content length</summary>

#### validates content length _(slow)_

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
<summary>Advanced: rejects invalid content length</summary>

#### rejects invalid content length _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_content_length(-1)
match result:
    case nil: fail("negative content length unexpectedly validated")
    case err: expect(err.message.contains("negative")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: validates string content</summary>

#### validates string content _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val validator = input_validator()
val result = validator.validate_string("test message")
expect(result).to_be_nil()
```

</details>


</details>

### TCP Transport - error handling

<details>
<summary>Advanced: creates connection error</summary>

#### creates connection error _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = mcp_error(ErrorCategory.Network, "Connection refused")
expect(err.category).to_equal(ErrorCategory.Network)
expect(err.message).to_equal("Connection refused")
```

</details>


</details>

<details>
<summary>Advanced: creates timeout error</summary>

#### creates timeout error _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = mcp_error(ErrorCategory.Timeout, "Read timeout")
expect(err.category).to_equal(ErrorCategory.Timeout)
```

</details>


</details>

<details>
<summary>Advanced: creates parse error for malformed data</summary>

#### creates parse error for malformed data _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = mcp_error(ErrorCategory.ParseError, "Invalid JSON received")
expect(err.category).to_equal(ErrorCategory.ParseError)
```

</details>


</details>

### TCP Transport - logging

<details>
<summary>Advanced: debug level for connection events</summary>

#### debug level for connection events _(slow)_

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
<summary>Advanced: info level for successful connections</summary>

#### info level for successful connections _(slow)_

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
<summary>Advanced: error level for connection failures</summary>

#### error level for connection failures _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(log_level_to_int("error")).to_equal(4)
```

</details>


</details>

### TCP Transport - escape for wire format

<details>
<summary>Advanced: escapes special characters</summary>

#### escapes special characters _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val escaped = escape_json("data{NL}with{NL}newlines")
expect(escaped.contains(NL)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: preserves normal data</summary>

#### preserves normal data _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json("normal")).to_equal("normal")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/transport_tcp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- TCP Transport - message building
- TCP Transport - response formatting
- TCP Transport - Content-Length framing
- TCP Transport - read operations
- TCP Transport - write operations
- TCP Transport - connection validation
- TCP Transport - error handling
- TCP Transport - logging
- TCP Transport - escape for wire format

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 25 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
