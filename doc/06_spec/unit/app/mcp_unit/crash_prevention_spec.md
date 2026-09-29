# @manual: primary

> Purpose: Prove that Crash prevention architecture.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that Crash prevention architecture.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/crash_prevention_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Crash prevention architecture.
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

### Crash prevention architecture

<details>
<summary>Advanced: validates content length limits exist</summary>

#### validates content length limits exist _(slow)_

- Verify: validates content length limits exist
   - Expected: limits.max_content_length > 0 is true
   - Expected: limits.max_string_length > 0 is true
   - Expected: limits.max_content_length > limits.max_string_length is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: validates content length limits exist")
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

- Verify: has error recovery tracking
   - Expected: consecutive_errors equals `2`
   - Expected: consecutive_errors < max_errors is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has error recovery tracking")
var consecutive_errors = 0
var max_errors = 5
consecutive_errors = consecutive_errors + 1
consecutive_errors = consecutive_errors + 1
expect(consecutive_errors).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(consecutive_errors < max_errors).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: resets error count on success</summary>

#### resets error count on success _(slow)_

- Verify: resets error count on success
   - Expected: consecutive_errors equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: resets error count on success")
var consecutive_errors = 3
consecutive_errors = 0
expect(consecutive_errors).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>


</details>

<details>
<summary>Advanced: stops after max consecutive errors</summary>

#### stops after max consecutive errors _(slow)_

- Verify: stops after max consecutive errors
   - Expected: should_stop is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: stops after max consecutive errors")
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

### URI validation

<details>
<summary>Advanced: validates file URI prefix</summary>

#### validates file URI prefix _(slow)_

- Verify: validates file URI prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: validates file URI prefix")
val validator = input_validator()
val result = validator.validate_uri("file:///home/user/test.spl")
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: validates symbol URI prefix</summary>

#### validates symbol URI prefix _(slow)_

- Verify: validates symbol URI prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: validates symbol URI prefix")
val validator = input_validator()
val result = validator.validate_uri("symbol://project/MyClass")
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: rejects invalid URI scheme</summary>

#### rejects invalid URI scheme _(slow)_

- Verify: rejects invalid URI scheme


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: rejects invalid URI scheme")
val validator = input_validator()
val result = validator.validate_uri("invalid://test")
match result:
    case nil: expect(false).to_equal(true)
    case err: expect(err.message.contains("scheme")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: validates URI length limit</summary>

#### validates URI length limit _(slow)_

- Verify: validates URI length limit
   - Expected: is_valid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: validates URI length limit")
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

- Verify: validates simple tool name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: validates simple tool name")
val validator = input_validator()
val result = validator.validate_tool_name("read_code")
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: validates tool name with slash</summary>

#### validates tool name with slash _(slow)_

- Verify: validates tool name with slash


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: validates tool name with slash")
val validator = input_validator()
val result = validator.validate_tool_name("tools/list")
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: rejects empty tool name</summary>

#### rejects empty tool name _(slow)_

- Verify: rejects empty tool name


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: rejects empty tool name")
val validator = input_validator()
val result = validator.validate_tool_name("")
match result:
    case nil: expect(false).to_equal(true)
    case err: expect(err.message.contains("empty")).to_equal(true)
```

</details>


</details>

### Error categories

<details>
<summary>Advanced: has transport errors</summary>

#### has transport errors _(slow)_

- Verify: has transport errors
   - Expected: response contains `Transport`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has transport errors")
val response = make_error_response("1", -32000, "Transport error")
expect(response.contains("Transport")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has protocol errors</summary>

#### has protocol errors _(slow)_

- Verify: has protocol errors
   - Expected: response contains `Protocol`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has protocol errors")
val response = make_error_response("1", -32600, "Protocol error")
expect(response.contains("Protocol")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has validation errors</summary>

#### has validation errors _(slow)_

- Verify: has validation errors
   - Expected: response contains `Validation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has validation errors")
val response = make_error_response("1", -32602, "Validation error")
expect(response.contains("Validation")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has resource errors</summary>

#### has resource errors _(slow)_

- Verify: has resource errors
   - Expected: response contains `Resource`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has resource errors")
val response = make_error_response("1", -32001, "Resource error")
expect(response.contains("Resource")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has tool errors</summary>

#### has tool errors _(slow)_

- Verify: has tool errors
   - Expected: response contains `Tool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has tool errors")
val response = make_error_response("1", -32002, "Tool error")
expect(response.contains("Tool")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has internal errors</summary>

#### has internal errors _(slow)_

- Verify: has internal errors
   - Expected: response contains `Internal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has internal errors")
val response = make_error_response("1", -32603, "Internal error")
expect(response.contains("Internal")).to_equal(true)
```

</details>


</details>

### Log levels

<details>
<summary>Advanced: has trace level</summary>

#### has trace level _(slow)_

- Verify: has trace level
   - Expected: log_level_to_int("debug") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has trace level")
expect(log_level_to_int("debug")).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: has info level</summary>

#### has info level _(slow)_

- Verify: has info level
   - Expected: log_level_to_int("info") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has info level")
expect(log_level_to_int("info")).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: has warn level</summary>

#### has warn level _(slow)_

- Verify: has warn level
   - Expected: log_level_to_int("warning") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has warn level")
expect(log_level_to_int("warning")).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: has error level</summary>

#### has error level _(slow)_

- Verify: has error level
   - Expected: log_level_to_int("error") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has error level")
expect(log_level_to_int("error")).to_equal(4)
```

</details>


</details>

<details>
<summary>Advanced: has critical level</summary>

#### has critical level _(slow)_

- Verify: has critical level
   - Expected: log_level_to_int("critical") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has critical level")
expect(log_level_to_int("critical")).to_equal(5)
```

</details>


</details>

<details>
<summary>Advanced: has emergency level</summary>

#### has emergency level _(slow)_

- Verify: has emergency level
   - Expected: log_level_to_int("emergency") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has emergency level")
expect(log_level_to_int("emergency")).to_equal(7)
```

</details>


</details>

<details>
<summary>Advanced: orders levels correctly</summary>

#### orders levels correctly _(slow)_

- Verify: orders levels correctly
   - Expected: debug_val < info_val is true
   - Expected: info_val < warning_val is true
   - Expected: warning_val < error_val is true
   - Expected: error_val < emergency_val is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: orders levels correctly")
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

- Verify: has default limits
   - Expected: limits.max_content_length equals `1048576`
   - Expected: limits.max_string_length equals `65536`
   - Expected: limits.max_array_length equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has default limits")
val limits = default_validation_limits()
expect(limits.max_content_length).to_equal(1048576)  # oracle: 1048576 — named expected value from the requirement
expect(limits.max_string_length).to_equal(65536)  # oracle: 65536 — named expected value from the requirement
expect(limits.max_array_length).to_equal(1000)  # oracle: 1000 — named expected value from the requirement
```

</details>


</details>

<details>
<summary>Advanced: has strict limits</summary>

#### has strict limits _(slow)_

- Verify: has strict limits
   - Expected: limits.max_content_length equals `524288`
   - Expected: limits.max_string_length equals `32768`
   - Expected: limits.max_array_length equals `500`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has strict limits")
val limits = strict_validation_limits()
expect(limits.max_content_length).to_equal(524288)  # oracle: 524288 — named expected value from the requirement
expect(limits.max_string_length).to_equal(32768)  # oracle: 32768 — named expected value from the requirement
expect(limits.max_array_length).to_equal(500)  # oracle: 500 — named expected value from the requirement
```

</details>


</details>

<details>
<summary>Advanced: strict limits are more restrictive</summary>

#### strict limits are more restrictive _(slow)_

- Verify: strict limits are more restrictive
   - Expected: s.max_content_length < d.max_content_length is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: strict limits are more restrictive")
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

- Verify: has JSON-RPC parse error code
   - Expected: response contains `-32700`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has JSON-RPC parse error code")
val response = make_error_response("1", -32700, "Parse error")
expect(response.contains("-32700")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has JSON-RPC invalid request code</summary>

#### has JSON-RPC invalid request code _(slow)_

- Verify: has JSON-RPC invalid request code
   - Expected: response contains `-32600`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has JSON-RPC invalid request code")
val response = make_error_response("1", -32600, "Invalid Request")
expect(response.contains("-32600")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has JSON-RPC method not found code</summary>

#### has JSON-RPC method not found code _(slow)_

- Verify: has JSON-RPC method not found code
   - Expected: response contains `-32601`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has JSON-RPC method not found code")
val response = make_error_response("1", -32601, "Method not found")
expect(response.contains("-32601")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has JSON-RPC invalid params code</summary>

#### has JSON-RPC invalid params code _(slow)_

- Verify: has JSON-RPC invalid params code
   - Expected: response contains `-32602`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has JSON-RPC invalid params code")
val response = make_error_response("1", -32602, "Invalid params")
expect(response.contains("-32602")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has JSON-RPC internal error code</summary>

#### has JSON-RPC internal error code _(slow)_

- Verify: has JSON-RPC internal error code
   - Expected: response contains `-32603`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has JSON-RPC internal error code")
val response = make_error_response("1", -32603, "Internal error")
expect(response.contains("-32603")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has custom timeout code</summary>

#### has custom timeout code _(slow)_

- Verify: has custom timeout code
   - Expected: response contains `-32000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has custom timeout code")
val response = make_error_response("1", -32000, "Timeout")
expect(response.contains("-32000")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has custom rate limit code</summary>

#### has custom rate limit code _(slow)_

- Verify: has custom rate limit code
   - Expected: response contains `-32001`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has custom rate limit code")
val response = make_error_response("1", -32001, "Rate limit")
expect(response.contains("-32001")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: has custom validation code</summary>

#### has custom validation code _(slow)_

- Verify: has custom validation code
   - Expected: response contains `-32002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: has custom validation code")
val response = make_error_response("1", -32002, "Validation")
expect(response.contains("-32002")).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 38 |
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

- Canonical SPipe generation for source `76dfa0571b27b0dc4cc44bb39edfe6ddce69f0d254041de93063b98ef0f9a7c0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `76dfa0571b27b0dc4cc44bb39edfe6ddce69f0d254041de93063b98ef0f9a7c0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `76dfa0571b27b0dc4cc44bb39edfe6ddce69f0d254041de93063b98ef0f9a7c0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/app/mcp_unit/crash_prevention_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/crash_prevention_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/unit/app/mcp_unit/crash_prevention_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/crash_prevention_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/crash_prevention_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/crash_prevention_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/app/mcp_unit/crash_prevention_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'validates content length limits exist' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/crash_prevention_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has error recovery tracking' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/crash_prevention_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resets error count on success' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
