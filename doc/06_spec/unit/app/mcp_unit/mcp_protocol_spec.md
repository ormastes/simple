# @manual: primary

> Purpose: Prove that MCP JSON-RPC 2.0 Protocol.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that MCP JSON-RPC 2.0 Protocol.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/mcp_protocol_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that MCP JSON-RPC 2.0 Protocol.
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

### MCP JSON-RPC 2.0 Protocol

#### when handling initialize request

#### builds response with protocol version

- Verify: builds response with protocol version
   - Expected: response contains `protocolVersion`
   - Expected: response contains `2025-06-18`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: builds response with protocol version")
val proto = "2025-06-18"
val result = jo1(jp("protocolVersion", js(proto)))
val response = make_result_response("1", result)
expect(response.contains("protocolVersion")).to_equal(true)
expect(response.contains("2025-06-18")).to_equal(true)
```

</details>

#### builds response with server information

- Verify: builds response with server information
   - Expected: server_info contains `simple-mcp`
   - Expected: server_info contains `2.0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: builds response with server information")
val server_info = jo2(jp("name", js("simple-mcp")), jp("version", js("2.0.0")))
expect(server_info.contains("simple-mcp")).to_equal(true)
expect(server_info.contains("2.0.0")).to_equal(true)
```

</details>

#### when handling tools/list request

#### builds tool list response

- Verify: builds tool list response
   - Expected: result contains `read_code`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: builds tool list response")
val tool = jo2(jp("name", js("read_code")), jp("description", js("Read file")))
val tools = "[" + tool + "]"
val result = jo1(jp("tools", tools))
expect(result.contains("read_code")).to_equal(true)
```

</details>

#### when handling errors

#### builds method not found error

- Verify: builds method not found error
   - Expected: response contains `-32601`
   - Expected: response contains `Method not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: builds method not found error")
val response = make_error_response("1", -32601, "Method not found")
expect(response.contains("-32601")).to_equal(true)
expect(response.contains("Method not found")).to_equal(true)
```

</details>

#### builds invalid params error

- Verify: builds invalid params error
   - Expected: response contains `-32602`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: builds invalid params error")
val response = make_error_response("1", -32602, "Invalid params")
expect(response.contains("-32602")).to_equal(true)
```

</details>

### MCP Message Format

#### when formatting responses

#### builds valid JSON response

- Verify: builds valid JSON response
   - Expected: response.starts_with(LB()) is true
   - Expected: response.ends_with(RB()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: builds valid JSON response")
val response = make_result_response("1", LB() + RB())
expect(response.starts_with(LB())).to_equal(true)
expect(response.ends_with(RB())).to_equal(true)
```

</details>

#### includes jsonrpc version in result response

- Verify: includes jsonrpc version in result response
   - Expected: response contains `"jsonrpc":"2.0"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: includes jsonrpc version in result response")
val response = make_result_response("1", "null")
expect(response.contains("\"jsonrpc\":\"2.0\"")).to_equal(true)
```

</details>

#### includes jsonrpc version in error response

- Verify: includes jsonrpc version in error response
   - Expected: response contains `"jsonrpc":"2.0"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: includes jsonrpc version in error response")
val response = make_error_response("1", -32600, "Bad request")
expect(response.contains("\"jsonrpc\":\"2.0\"")).to_equal(true)
```

</details>

### MCP Capability Negotiation

#### when server declares capabilities

#### builds capabilities JSON

- Verify: builds capabilities JSON
   - Expected: caps contains `"tools"`
   - Expected: caps contains `"resources"`
   - Expected: caps contains `"prompts"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: builds capabilities JSON")
val tools_cap = jo1("")
val resources_cap = jo1("")
val prompts_cap = jo1("")
val caps = jo3(jp("tools", tools_cap), jp("resources", resources_cap), jp("prompts", prompts_cap))
expect(caps.contains("\"tools\"")).to_equal(true)
expect(caps.contains("\"resources\"")).to_equal(true)
expect(caps.contains("\"prompts\"")).to_equal(true)
```

</details>

### MCP Request ID Handling

#### when request has string ID

#### preserves string ID in response

- Verify: preserves string ID in response
   - Expected: response contains `"id":"test-123"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: preserves string ID in response")
val response = make_result_response("\"test-123\"", "null")
expect(response.contains("\"id\":\"test-123\"")).to_equal(true)
```

</details>

#### when request has numeric ID

#### preserves numeric ID in response

- Verify: preserves numeric ID in response
   - Expected: response contains `"id":42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: preserves numeric ID in response")
val response = make_result_response("42", "null")
expect(response.contains("\"id\":42")).to_equal(true)
```

</details>

### MCP Method Routing

#### when extracting method from request

#### extracts method field

- Verify: extracts method field
   - Expected: method equals `initialize`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: extracts method field")
val req = jo2(jp("method", js("initialize")), jp("id", "1"))
val method = extract_json_string(req, "method")
expect(method).to_equal("initialize")
```

</details>

#### extracts tools/list method

- Verify: extracts tools/list method
   - Expected: method equals `tools/list`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: extracts tools/list method")
val req = jo2(jp("method", js("tools/list")), jp("id", "2"))
val method = extract_json_string(req, "method")
expect(method).to_equal("tools/list")
```

</details>

#### extracts tools/call method

- Verify: extracts tools/call method
   - Expected: method equals `tools/call`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: extracts tools/call method")
val req = jo2(jp("method", js("tools/call")), jp("id", "3"))
val method = extract_json_string(req, "method")
expect(method).to_equal("tools/call")
```

</details>

### Log Level Utilities

<details>
<summary>Advanced: maps debug to 0</summary>

#### maps debug to 0 _(slow)_

- Verify: maps debug to 0
   - Expected: log_level_to_int("debug") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: maps debug to 0")
expect(log_level_to_int("debug")).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: maps info to 1</summary>

#### maps info to 1 _(slow)_

- Verify: maps info to 1
   - Expected: log_level_to_int("info") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: maps info to 1")
expect(log_level_to_int("info")).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: maps warning to 3</summary>

#### maps warning to 3 _(slow)_

- Verify: maps warning to 3
   - Expected: log_level_to_int("warning") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: maps warning to 3")
expect(log_level_to_int("warning")).to_equal(3)
```

</details>


</details>

<details>
<summary>Advanced: maps error to 4</summary>

#### maps error to 4 _(slow)_

- Verify: maps error to 4
   - Expected: log_level_to_int("error") equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: maps error to 4")
expect(log_level_to_int("error")).to_equal(4)
```

</details>


</details>

<details>
<summary>Advanced: maps critical to 5</summary>

#### maps critical to 5 _(slow)_

- Verify: maps critical to 5
   - Expected: log_level_to_int("critical") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: maps critical to 5")
expect(log_level_to_int("critical")).to_equal(5)
```

</details>


</details>

<details>
<summary>Advanced: returns -1 for unknown level</summary>

#### returns -1 for unknown level _(slow)_

- Verify: returns -1 for unknown level
   - Expected: log_level_to_int("unknown") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: returns -1 for unknown level")
expect(log_level_to_int("unknown")).to_equal(-1)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 6 |
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

- Canonical SPipe generation for source `59a5572865a7c4b349571f1faf60a029908d14894f165fc4e0c118a923a423b4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `59a5572865a7c4b349571f1faf60a029908d14894f165fc4e0c118a923a423b4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `59a5572865a7c4b349571f1faf60a029908d14894f165fc4e0c118a923a423b4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/app/mcp_unit/mcp_protocol_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_protocol_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/unit/app/mcp_unit/mcp_protocol_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_protocol_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_protocol_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/mcp_protocol_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/app/mcp_unit/mcp_protocol_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds response with protocol version' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_protocol_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds response with server information' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_protocol_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds tool list response' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
