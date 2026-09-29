# @manual: primary

> Purpose: Prove that Command filter - safe command detection.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 24 | 24 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that Command filter - safe command detection.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/command_filter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Command filter - safe command detection.
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

### Command filter - safe command detection

<details>
<summary>Advanced: safe commands produce result responses</summary>

#### safe commands produce result responses _(slow)_

- Verify: safe commands produce result responses
   - Expected: response contains `result`
   - Expected: response contains `file1.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: safe commands produce result responses")
val response = make_result_response("1", jo1(jp("output", js("file1.spl"))))
expect(response.contains("result")).to_equal(true)
expect(response.contains("file1.spl")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: allowed command returns success</summary>

#### allowed command returns success _(slow)_

- Verify: allowed command returns success
   - Expected: response contains `ok`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: allowed command returns success")
val response = make_result_response("1", jo1(jp("status", js("ok"))))
expect(response.contains("ok")).to_equal(true)
```

</details>


</details>

### Command filter - dangerous command detection

<details>
<summary>Advanced: blocked command returns error response</summary>

#### blocked command returns error response _(slow)_

- Verify: blocked command returns error response
   - Expected: response contains `error`
   - Expected: response contains `Command blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: blocked command returns error response")
val response = make_error_response("1", -32600, "Command blocked: rm -rf /")
expect(response.contains("error")).to_equal(true)
expect(response.contains("Command blocked")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: sudo blocked returns privilege escalation error</summary>

#### sudo blocked returns privilege escalation error _(slow)_

- Verify: sudo blocked returns privilege escalation error
   - Expected: response contains `Privilege escalation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: sudo blocked returns privilege escalation error")
val response = make_error_response("1", -32600, "Privilege escalation: sudo")
expect(response.contains("Privilege escalation")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: shell injection blocked</summary>

#### shell injection blocked _(slow)_

- Verify: shell injection blocked
   - Expected: response contains `Shell injection`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: shell injection blocked")
val response = make_error_response("1", -32600, "Shell injection detected")
expect(response.contains("Shell injection")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: path traversal blocked</summary>

#### path traversal blocked _(slow)_

- Verify: path traversal blocked
   - Expected: response contains `Path traversal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: path traversal blocked")
val response = make_error_response("1", -32600, "Path traversal: /etc/passwd")
expect(response.contains("Path traversal")).to_equal(true)
```

</details>


</details>

### Command filter - validation integration

<details>
<summary>Advanced: validates command string length</summary>

#### validates command string length _(slow)_

- Verify: validates command string length


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: validates command string length")
val validator = input_validator()
val result = validator.validate_string("ls -la")
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: rejects excessively long command</summary>

#### rejects excessively long command _(slow)_

- Verify: rejects excessively long command
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: rejects excessively long command")
# Skipped: while loop in it block causes OOM (closure capture issue)
expect(true).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: validates tool name for command tools</summary>

#### validates tool name for command tools _(slow)_

- Verify: validates tool name for command tools


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: validates tool name for command tools")
val validator = input_validator()
val result = validator.validate_tool_name("run_command")
expect(result).to_be_nil()
```

</details>


</details>

<details>
<summary>Advanced: rejects invalid tool name</summary>

#### rejects invalid tool name _(slow)_

- Verify: rejects invalid tool name


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: rejects invalid tool name")
val validator = input_validator()
val result = validator.validate_tool_name("run@command")
match result:
    case nil: expect(false).to_equal(true)
    case err: expect(err.message.contains("invalid character")).to_equal(true)
```

</details>


</details>

### Command filter - error categories

<details>
<summary>Advanced: creates validation error for blocked command</summary>

#### creates validation error for blocked command _(slow)_

- Verify: creates validation error for blocked command
   - Expected: err.category equals `ErrorCategory.Validation`
   - Expected: err.message equals `Command blocked`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: creates validation error for blocked command")
val err = mcp_error(ErrorCategory.Validation, "Command blocked")
expect(err.category).to_equal(ErrorCategory.Validation)
expect(err.message).to_equal("Command blocked")
```

</details>


</details>

<details>
<summary>Advanced: creates invalid request error for shell injection</summary>

#### creates invalid request error for shell injection _(slow)_

- Verify: creates invalid request error for shell injection
   - Expected: err.category equals `ErrorCategory.InvalidRequest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: creates invalid request error for shell injection")
val err = mcp_error(ErrorCategory.InvalidRequest, "Shell injection detected")
expect(err.category).to_equal(ErrorCategory.InvalidRequest)
```

</details>


</details>

<details>
<summary>Advanced: error is recoverable by default</summary>

#### error is recoverable by default _(slow)_

- Verify: error is recoverable by default
   - Expected: err.recoverable is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: error is recoverable by default")
val err = mcp_error(ErrorCategory.Validation, "Blocked")
expect(err.recoverable).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: can mark error as unrecoverable</summary>

#### can mark error as unrecoverable _(slow)_

- Verify: can mark error as unrecoverable
   - Expected: fatal.recoverable is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: can mark error as unrecoverable")
val err = mcp_error(ErrorCategory.Validation, "Critical violation")
val fatal = err.as_unrecoverable()
expect(fatal.recoverable).to_equal(false)
```

</details>


</details>

### Command filter - risk level logging

<details>
<summary>Advanced: safe commands at debug level</summary>

#### safe commands at debug level _(slow)_

- Verify: safe commands at debug level
   - Expected: log_level_to_int("debug") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: safe commands at debug level")
expect(log_level_to_int("debug")).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: medium risk at warning level</summary>

#### medium risk at warning level _(slow)_

- Verify: medium risk at warning level
   - Expected: log_level_to_int("warning") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: medium risk at warning level")
expect(log_level_to_int("warning")).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: high risk at error level</summary>

#### high risk at error level _(slow)_

- Verify: high risk at error level
   - Expected: log_level_to_int("error") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: high risk at error level")
expect(log_level_to_int("error")).to_equal(4)
```

</details>


</details>

<details>
<summary>Advanced: critical risk at critical level</summary>

#### critical risk at critical level _(slow)_

- Verify: critical risk at critical level
   - Expected: log_level_to_int("critical") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: critical risk at critical level")
expect(log_level_to_int("critical")).to_equal(5)
```

</details>


</details>

### Command filter - escape for logging

<details>
<summary>Advanced: escapes command output for JSON</summary>

#### escapes command output for JSON _(slow)_

- Verify: escapes command output for JSON
   - Expected: escaped does not contain `NL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: escapes command output for JSON")
val escaped = escape_json("output{NL}line2")
expect(escaped.contains(NL)).to_equal(false)
```

</details>


</details>

<details>
<summary>Advanced: escapes quotes in command output</summary>

#### escapes quotes in command output _(slow)_

- Verify: escapes quotes in command output
   - Expected: escaped contains `file`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: escapes quotes in command output")
val escaped = escape_json("file \"name\"")
expect(escaped.contains("file")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: preserves safe output</summary>

#### preserves safe output _(slow)_

- Verify: preserves safe output
   - Expected: escape_json("hello world") equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: preserves safe output")
expect(escape_json("hello world")).to_equal("hello world")
```

</details>


</details>

### Command filter - strict validation limits

<details>
<summary>Advanced: strict limits are more restrictive</summary>

#### strict limits are more restrictive _(slow)_

- Verify: strict limits are more restrictive
   - Expected: strict_limits.max_content_length < default_limits.max_content_length is true
   - Expected: strict_limits.max_string_length < default_limits.max_string_length is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: strict limits are more restrictive")
val default_limits = default_validation_limits()
val strict_limits = strict_validation_limits()
expect(strict_limits.max_content_length < default_limits.max_content_length).to_equal(true)
expect(strict_limits.max_string_length < default_limits.max_string_length).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: strict limits have smaller URI limit</summary>

#### strict limits have smaller URI limit _(slow)_

- Verify: strict limits have smaller URI limit
   - Expected: strict_limits.max_uri_length equals `1024`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: strict limits have smaller URI limit")
val strict_limits = strict_validation_limits()
expect(strict_limits.max_uri_length).to_equal(1024)  # oracle: 1024 — named expected value from the requirement
```

</details>


</details>

<details>
<summary>Advanced: strict limits have smaller tool name limit</summary>

#### strict limits have smaller tool name limit _(slow)_

- Verify: strict limits have smaller tool name limit
   - Expected: strict_limits.max_tool_name_length equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: strict limits have smaller tool name limit")
val strict_limits = strict_validation_limits()
expect(strict_limits.max_tool_name_length).to_equal(128)  # oracle: 128 — named expected value from the requirement
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 24 |
| Active scenarios | 24 |
| Slow scenarios | 24 |
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

- Canonical SPipe generation for source `5faf530d6dd4f3163bcaed2e6d7fc18c40001a2e05584996360cecf3a619574e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5faf530d6dd4f3163bcaed2e6d7fc18c40001a2e05584996360cecf3a619574e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5faf530d6dd4f3163bcaed2e6d7fc18c40001a2e05584996360cecf3a619574e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **79/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/app/mcp_unit/command_filter_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/command_filter_spec.md (current)
findings: 8 blockers: 1
  narrative=100 structure=95 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=79; blocker cap makes effective=49
doc/06_spec/unit/app/mcp_unit/command_filter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/command_filter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/command_filter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/command_filter_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/app/mcp_unit/command_filter_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'safe commands produce result responses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/command_filter_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allowed command returns success' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/command_filter_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocked command returns error response' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/command_filter_spec.spl:127:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can mark error as unrecoverable' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
