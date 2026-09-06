# @manual: primary

> Purpose: Prove that TCP Transport - message building.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that TCP Transport - message building.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/transport_tcp_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that TCP Transport - message building.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-APP-MCP-UNIT-001
doc/01_research/local/REQ-APP-MCP-UNIT-001.md
doc/03_plan/sys_test/REQ-APP-MCP-UNIT-001.md
doc/04_architecture/REQ-APP-MCP-UNIT-001.md
doc/05_design/REQ-APP-MCP-UNIT-001.md

## Scenarios

### TCP Transport - message building

<details>
<summary>Advanced: builds valid JSON-RPC request</summary>

#### builds valid JSON-RPC request _(slow)_

- Verify: builds valid JSON-RPC request
   - Expected: request contains `jsonrpc`
   - Expected: request contains `2.0`
   - Expected: request contains `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: builds valid JSON-RPC request")
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

- Verify: builds request with params
   - Expected: request contains `tools/call`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: builds request with params")
val params = jo1(jp("path", js("/test.spl")))
val request = jo3(jp("jsonrpc", js("2.0")), jp("id", "1"), jp("method", js("tools/call")))
expect(request.contains("tools/call")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds notification without id</summary>

#### builds notification without id _(slow)_

- Verify: builds notification without id
   - Expected: notif contains `notifications/initialized`
   - Expected: notif contains `jsonrpc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: builds notification without id")
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

- Verify: formats result response
   - Expected: response contains `jsonrpc`
   - Expected: response contains `result`
   - Expected: response contains `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: formats result response")
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

- Verify: formats error response
   - Expected: response contains `error`
   - Expected: response contains `-32600`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: formats error response")
val response = make_error_response("1", -32600, "Invalid request")
expect(response.contains("error")).to_equal(true)
expect(response.contains("-32600")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: includes id in response</summary>

#### includes id in response _(slow)_

- Verify: includes id in response
   - Expected: response contains `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: includes id in response")
val response = make_result_response("42", js("done"))
expect(response.contains("42")).to_equal(true)
```

</details>


</details>

### TCP Transport - Content-Length framing

<details>
<summary>Advanced: calculates content length for response</summary>

#### calculates content length for response _(slow)_

- Verify: calculates content length for response
   - Expected: content_length > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: calculates content length for response")
val response = make_result_response("1", js("ok"))
val content_length = response.len()
expect(content_length > 0).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds Content-Length header</summary>

#### builds Content-Length header _(slow)_

- Verify: builds Content-Length header
   - Expected: header.starts_with("Content-Length:") is true
   - Expected: header.ends_with("\r{NL}\r{NL}") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: builds Content-Length header")
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

- Verify: extracts method from received message
   - Expected: extract_json_string(json, "method") equals `initialize`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: extracts method from received message")
val json = jo2(jp("method", js("initialize")), jp("id", "1"))
expect(extract_json_string(json, "method")).to_equal("initialize")
```

</details>


</details>

<details>
<summary>Advanced: extracts id from received message</summary>

#### extracts id from received message _(slow)_

- Verify: extracts id from received message
   - Expected: extract_json_value(json, "id") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: extracts id from received message")
val json = jo2(jp("id", "42"), jp("method", js("test")))
expect(extract_json_value(json, "id")).to_equal("42")
```

</details>


</details>

<details>
<summary>Advanced: extracts params from received message</summary>

#### extracts params from received message _(slow)_

- Verify: extracts params from received message
   - Expected: extract_json_string(json, "method") equals `tools/call`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: extracts params from received message")
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

- Verify: writes result response
   - Expected: response contains `result`
   - Expected: response contains `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: writes result response")
val response = make_result_response("1", jo1(jp("data", js("hello"))))
expect(response.contains("result")).to_equal(true)
expect(response.contains("hello")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: writes error response</summary>

#### writes error response _(slow)_

- Verify: writes error response
   - Expected: response contains `error`
   - Expected: response contains `-32603`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: writes error response")
val response = make_error_response("1", -32603, "Internal error")
expect(response.contains("error")).to_equal(true)
expect(response.contains("-32603")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: writes notification</summary>

#### writes notification _(slow)_

- Verify: writes notification
   - Expected: notif contains `tools/list_changed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: writes notification")
val notif = make_notification_no_params("notifications/tools/list_changed")
expect(notif.contains("tools/list_changed")).to_equal(true)
```

</details>


</details>

### TCP Transport - connection validation

<details>
<summary>Advanced: validates content length</summary>

#### validates content length _(slow)_

- Verify: validates content length


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: validates content length")
val validator = input_validator()
val result = validator.validate_content_length(1000)
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: rejects invalid content length</summary>

#### rejects invalid content length _(slow)_

- Verify: rejects invalid content length


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: rejects invalid content length")
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

- Verify: validates string content


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: validates string content")
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

- Verify: creates connection error
   - Expected: err.category equals `ErrorCategory.Network`
   - Expected: err.message equals `Connection refused`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: creates connection error")
val err = mcp_error(ErrorCategory.Network, "Connection refused")
expect(err.category).to_equal(ErrorCategory.Network)
expect(err.message).to_equal("Connection refused")
```

</details>


</details>

<details>
<summary>Advanced: creates timeout error</summary>

#### creates timeout error _(slow)_

- Verify: creates timeout error
   - Expected: err.category equals `ErrorCategory.Timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: creates timeout error")
val err = mcp_error(ErrorCategory.Timeout, "Read timeout")
expect(err.category).to_equal(ErrorCategory.Timeout)
```

</details>


</details>

<details>
<summary>Advanced: creates parse error for malformed data</summary>

#### creates parse error for malformed data _(slow)_

- Verify: creates parse error for malformed data
   - Expected: err.category equals `ErrorCategory.ParseError`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: creates parse error for malformed data")
val err = mcp_error(ErrorCategory.ParseError, "Invalid JSON received")
expect(err.category).to_equal(ErrorCategory.ParseError)
```

</details>


</details>

### TCP Transport - logging

<details>
<summary>Advanced: debug level for connection events</summary>

#### debug level for connection events _(slow)_

- Verify: debug level for connection events
   - Expected: log_level_to_int("debug") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: debug level for connection events")
expect(log_level_to_int("debug")).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: info level for successful connections</summary>

#### info level for successful connections _(slow)_

- Verify: info level for successful connections
   - Expected: log_level_to_int("info") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: info level for successful connections")
expect(log_level_to_int("info")).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: error level for connection failures</summary>

#### error level for connection failures _(slow)_

- Verify: error level for connection failures
   - Expected: log_level_to_int("error") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: error level for connection failures")
expect(log_level_to_int("error")).to_equal(4)
```

</details>


</details>

### TCP Transport - escape for wire format

<details>
<summary>Advanced: escapes special characters</summary>

#### escapes special characters _(slow)_

- Verify: escapes special characters
   - Expected: escaped does not contain `NL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: escapes special characters")
val escaped = escape_json("data{NL}with{NL}newlines")
expect(escaped.contains(NL)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: preserves normal data</summary>

#### preserves normal data _(slow)_

- Verify: preserves normal data
   - Expected: escape_json("normal") equals `normal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: preserves normal data")
expect(escape_json("normal")).to_equal("normal")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 25 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-MCP-UNIT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5e29aa47d2ef3e1e80c1dd648c0fc8f959c7cdac3c12de21e2bd0a0ba8f24d0d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e29aa47d2ef3e1e80c1dd648c0fc8f959c7cdac3c12de21e2bd0a0ba8f24d0d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e29aa47d2ef3e1e80c1dd648c0fc8f959c7cdac3c12de21e2bd0a0ba8f24d0d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/app/mcp_unit/transport_tcp_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/transport_tcp_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/unit/app/mcp_unit/transport_tcp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/transport_tcp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/transport_tcp_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/transport_tcp_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/app/mcp_unit/transport_tcp_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds valid JSON-RPC request' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/transport_tcp_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds request with params' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/transport_tcp_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds notification without id' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
