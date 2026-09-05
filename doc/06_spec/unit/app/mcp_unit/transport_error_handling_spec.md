# @manual: primary

> Purpose: Prove that Transport Error Handling - Content-Length validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that Transport Error Handling - Content-Length validation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/transport_error_handling_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Transport Error Handling - Content-Length validation.
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

### Transport Error Handling - Content-Length validation

<details>
<summary>Advanced: rejects negative content length</summary>

#### rejects negative content length _(slow)_

- Verify: rejects negative content length


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: rejects negative content length")
val validator = input_validator()
val result = validator.validate_content_length(-100)
match result:
    case nil: expect(false).to_equal(true)
    case err: expect(err.message.contains("negative")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: accepts zero content length</summary>

#### accepts zero content length _(slow)_

- Verify: accepts zero content length


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: accepts zero content length")
val validator = input_validator()
val result = validator.validate_content_length(0)
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: accepts valid content length</summary>

#### accepts valid content length _(slow)_

- Verify: accepts valid content length


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: accepts valid content length")
val validator = input_validator()
val result = validator.validate_content_length(1000)
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: rejects excessive content length</summary>

#### rejects excessive content length _(slow)_

- Verify: rejects excessive content length


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: rejects excessive content length")
val validator = input_validator()
val result = validator.validate_content_length(2000000)
match result:
    case nil: expect(false).to_equal(true)
    case err: expect(err.message.contains("exceeds")).to_equal(true)
```

</details>


</details>

### Transport Error Handling - JSON-RPC ID handling

<details>
<summary>Advanced: extracts integer ID from JSON</summary>

#### extracts integer ID from JSON _(slow)_

- Verify: extracts integer ID from JSON
   - Expected: extract_json_value(json, "id") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: extracts integer ID from JSON")
val json = jo2(jp("id", "42"), jp("method", js("test")))
expect(extract_json_value(json, "id")).to_equal("42")
```

</details>


</details>

<details>
<summary>Advanced: handles null ID for notifications</summary>

#### handles null ID for notifications _(slow)_

- Verify: handles null ID for notifications
   - Expected: id equals `null`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: handles null ID for notifications")
val json = jo1(jp("method", js("notifications/initialized")))
val id = extract_json_value(json, "id")
expect(id).to_equal("null")
```

</details>


</details>

<details>
<summary>Advanced: extracts method from request</summary>

#### extracts method from request _(slow)_

- Verify: extracts method from request
   - Expected: extract_json_string(json, "method") equals `initialize`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: extracts method from request")
val json = jo2(jp("id", "1"), jp("method", js("initialize")))
expect(extract_json_string(json, "method")).to_equal("initialize")
```

</details>


</details>

### Transport Error Handling - malformed JSON responses

<details>
<summary>Advanced: creates parse error response</summary>

#### creates parse error response _(slow)_

- Verify: creates parse error response
   - Expected: response contains `-32700`
   - Expected: response contains `Parse error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: creates parse error response")
val response = make_error_response("null", -32700, "Parse error")
expect(response.contains("-32700")).to_equal(true)
expect(response.contains("Parse error")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: creates invalid request response</summary>

#### creates invalid request response _(slow)_

- Verify: creates invalid request response
   - Expected: response contains `-32600`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: creates invalid request response")
val response = make_error_response("1", -32600, "Invalid Request")
expect(response.contains("-32600")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: creates method not found response</summary>

#### creates method not found response _(slow)_

- Verify: creates method not found response
   - Expected: response contains `-32601`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: creates method not found response")
val response = make_error_response("1", -32601, "Method not found")
expect(response.contains("-32601")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: creates invalid params response</summary>

#### creates invalid params response _(slow)_

- Verify: creates invalid params response
   - Expected: response contains `-32602`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: creates invalid params response")
val response = make_error_response("1", -32602, "Invalid params")
expect(response.contains("-32602")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: creates internal error response</summary>

#### creates internal error response _(slow)_

- Verify: creates internal error response
   - Expected: response contains `-32603`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: creates internal error response")
val response = make_error_response("1", -32603, "Internal error")
expect(response.contains("-32603")).to_equal(true)
```

</details>


</details>

### Transport Error Handling - error categories

<details>
<summary>Advanced: parse error category</summary>

#### parse error category _(slow)_

- Verify: parse error category
   - Expected: err.category equals `ErrorCategory.ParseError`
   - Expected: json contains `-32700`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: parse error category")
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

- Verify: invalid request category
   - Expected: err.category equals `ErrorCategory.InvalidRequest`
   - Expected: json contains `-32600`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: invalid request category")
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

- Verify: validation error category
   - Expected: err.category equals `ErrorCategory.Validation`
   - Expected: json contains `-32002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: validation error category")
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

- Verify: timeout error category
   - Expected: err.category equals `ErrorCategory.Timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: timeout error category")
val err = mcp_error(ErrorCategory.Timeout, "Request timed out")
expect(err.category).to_equal(ErrorCategory.Timeout)
```

</details>


</details>

### Transport Error Handling - character classification

<details>
<summary>Advanced: newline character in escape</summary>

#### newline character in escape _(slow)_

- Verify: newline character in escape
   - Expected: escaped does not contain `NL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: newline character in escape")
val escaped = escape_json("line1{NL}line2")
expect(escaped.contains(NL)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: tab character in escape</summary>

#### tab character in escape _(slow)_

- Verify: tab character in escape
   - Expected: escaped does not contain `\t`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: tab character in escape")
val escaped = escape_json("col1\tcol2")
expect(escaped.contains("\t")).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: normal characters unchanged</summary>

#### normal characters unchanged _(slow)_

- Verify: normal characters unchanged
   - Expected: escape_json("hello") equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: normal characters unchanged")
expect(escape_json("hello")).to_equal("hello")
```

</details>


</details>

<details>
<summary>Advanced: empty string unchanged</summary>

#### empty string unchanged _(slow)_

- Verify: empty string unchanged
   - Expected: escape_json("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: empty string unchanged")
expect(escape_json("")).to_equal("")
```

</details>


</details>

### Transport Error Handling - logging for errors

<details>
<summary>Advanced: debug level for transport trace</summary>

#### debug level for transport trace _(slow)_

- Verify: debug level for transport trace
   - Expected: log_level_to_int("debug") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: debug level for transport trace")
expect(log_level_to_int("debug")).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: warning level for malformed input</summary>

#### warning level for malformed input _(slow)_

- Verify: warning level for malformed input
   - Expected: log_level_to_int("warning") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: warning level for malformed input")
expect(log_level_to_int("warning")).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: error level for transport failures</summary>

#### error level for transport failures _(slow)_

- Verify: error level for transport failures
   - Expected: log_level_to_int("error") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: error level for transport failures")
expect(log_level_to_int("error")).to_equal(4)
```

</details>


</details>

<details>
<summary>Advanced: critical level for unrecoverable errors</summary>

#### critical level for unrecoverable errors _(slow)_

- Verify: critical level for unrecoverable errors
   - Expected: log_level_to_int("critical") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: critical level for unrecoverable errors")
expect(log_level_to_int("critical")).to_equal(5)
```

</details>


</details>

### Transport Error Handling - error details

<details>
<summary>Advanced: attaches details to error</summary>

#### attaches details to error _(slow)_

- Verify: attaches details to error
   - Expected: detailed.details equals `Unexpected token at position 42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: attaches details to error")
val err = mcp_error(ErrorCategory.ParseError, "Invalid JSON")
val detailed = err.with_details("Unexpected token at position 42")
expect(detailed.details).to_equal("Unexpected token at position 42")
```

</details>


</details>

<details>
<summary>Advanced: marks error as unrecoverable</summary>

#### marks error as unrecoverable _(slow)_

- Verify: marks error as unrecoverable
   - Expected: fatal.recoverable is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: marks error as unrecoverable")
val err = mcp_error(ErrorCategory.InternalError, "Fatal")
val fatal = err.as_unrecoverable()
expect(fatal.recoverable).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: default error is recoverable</summary>

#### default error is recoverable _(slow)_

- Verify: default error is recoverable
   - Expected: err.recoverable is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: default error is recoverable")
val err = mcp_error(ErrorCategory.ParseError, "Parse failed")
expect(err.recoverable).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 27 |
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

- Canonical SPipe generation for source `3b73b3fa2dc3d393bf79caec0b51087c9246f497ccad5dcdb92c0775a323ec5a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3b73b3fa2dc3d393bf79caec0b51087c9246f497ccad5dcdb92c0775a323ec5a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3b73b3fa2dc3d393bf79caec0b51087c9246f497ccad5dcdb92c0775a323ec5a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/app/mcp_unit/transport_error_handling_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/transport_error_handling_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/unit/app/mcp_unit/transport_error_handling_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/transport_error_handling_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/transport_error_handling_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/transport_error_handling_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/app/mcp_unit/transport_error_handling_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative content length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/transport_error_handling_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts zero content length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/transport_error_handling_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts valid content length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
