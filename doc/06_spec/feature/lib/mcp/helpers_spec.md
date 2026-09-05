# MCP Library Helpers

> Tests the MCP library helper functions including JSON-RPC message construction, parameter validation, and response formatting. Verifies that helper utilities correctly build well-formed protocol messages for MCP communication.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Library Helpers

Tests the MCP library helper functions including JSON-RPC message construction, parameter validation, and response formatting. Verifies that helper utilities correctly build well-formed protocol messages for MCP communication.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | In Progress |
| Source | `test/feature/lib/mcp/helpers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the MCP library helper functions including JSON-RPC message construction,
parameter validation, and response formatting. Verifies that helper utilities
correctly build well-formed protocol messages for MCP communication.

## Scenarios

### MCP Library - Helpers

#### provides brace helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- provides brace helpers
- provides brace helpers
   - Expected: LB() equals `{`
   - Expected: RB() equals `}`
   - Expected: Q() equals `"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("provides brace helpers")
step("provides brace helpers")
# @req: REQ-FEAT-MCP-HELPERS-SPEC-001
expect(LB()).to_equal("{")
expect(RB()).to_equal("}")
expect(Q()).to_equal("\"")
```

</details>

#### parses integers

- parses integers
- parses integers
   - Expected: parse_int("123") equals `123`
   - Expected: parse_int("0") equals `0`
   - Expected: parse_int("999") equals `999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses integers")
step("parses integers")
expect(parse_int("123")).to_equal(123)
expect(parse_int("0")).to_equal(0)
expect(parse_int("999")).to_equal(999)
```

</details>

#### calculates minimum

- calculates minimum
- calculates minimum
   - Expected: min_int(5, 10) equals `5`
   - Expected: min_int(10, 5) equals `5`
   - Expected: min_int(7, 7) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calculates minimum")
step("calculates minimum")
expect(min_int(5, 10)).to_equal(5)
expect(min_int(10, 5)).to_equal(5)
expect(min_int(7, 7)).to_equal(7)
```

</details>

#### builds JSON pairs

- builds JSON pairs
- builds JSON pairs
   - Expected: jp("key", "value") equals `"key":value`
   - Expected: js("text") equals `"text"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("builds JSON pairs")
step("builds JSON pairs")
expect(jp("key", "value")).to_equal("\"key\":value")
expect(js("text")).to_equal("\"text\"")
```

</details>

#### builds JSON objects

- builds JSON objects
- builds JSON objects
   - Expected: obj equals `{"a":1,"b":2}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("builds JSON objects")
step("builds JSON objects")
val obj = jo2(jp("a", "1"), jp("b", "2"))
expect(obj).to_equal("{\"a\":1,\"b\":2}")
```

</details>

#### extracts JSON strings

- extracts JSON strings
- extracts JSON strings
   - Expected: extract_json_string_v2(json, "method") equals `initialize`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("extracts JSON strings")
step("extracts JSON strings")
val json = "{\"method\":\"initialize\",\"id\":1}"
expect(extract_json_string_v2(json, "method")).to_equal("initialize")
```

</details>

#### extracts JSON values

- extracts JSON values
- extracts JSON values
   - Expected: extract_json_value(json, "id") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("extracts JSON values")
step("extracts JSON values")
val json = "{\"id\":42,\"name\":\"test\"}"
expect(extract_json_value(json, "id")).to_equal("42")
```

</details>

#### creates result responses

- creates result responses
- creates result responses


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates result responses")
step("creates result responses")
val response = make_result_response("1", "{\"status\":\"ok\"}")
expect(response).to_contain("\"jsonrpc\":\"2.0\"")
expect(response).to_contain("\"id\":1")
expect(response).to_contain("\"result\":{\"status\":\"ok\"}")
```

</details>

#### creates error responses

- creates error responses
- creates error responses


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates error responses")
step("creates error responses")
val response = make_error_response("2", -32600, "Invalid request")
expect(response).to_contain("\"jsonrpc\":\"2.0\"")
expect(response).to_contain("\"id\":2")
expect(response).to_contain("\"error\"")
expect(response).to_contain("-32600")
```

</details>

#### creates tool results

- creates tool results
- creates tool results


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates tool results")
step("creates tool results")
val result = make_tool_result("42", "Output text")
expect(result).to_contain("\"jsonrpc\":\"2.0\"")
expect(result).to_contain("\"id\":42")
expect(result).to_contain("\"type\":\"text\"")
expect(result).to_contain("\"text\":\"Output text\"")
```

</details>

#### extracts arguments from request body

- extracts arguments from request body
- extracts arguments from request body
   - Expected: path equals `test.spl`
   - Expected: name equals `value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("extracts arguments from request body")
step("extracts arguments from request body")
val body = "{\"params\":{\"arguments\":{\"path\":\"test.spl\",\"name\":\"value\"}}}"
val path = extract_arg(body, "path")
val name = extract_arg(body, "name")
expect(path).to_equal("test.spl")
expect(name).to_equal("value")
```

</details>

#### returns empty string for missing arguments

- returns empty string for missing arguments
- returns empty string for missing arguments
   - Expected: missing equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns empty string for missing arguments")
step("returns empty string for missing arguments")
val body = "{\"params\":{\"arguments\":{\"path\":\"test.spl\"}}}"
val missing = extract_arg(body, "nonexistent")
expect(missing).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-MCP-HELPERS-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `45ed561d33d612d3aff1f3d32b4a15de476ab8260ec47a5dc6eba38feb299b00`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `45ed561d33d612d3aff1f3d32b4a15de476ab8260ec47a5dc6eba38feb299b00`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `45ed561d33d612d3aff1f3d32b4a15de476ab8260ec47a5dc6eba38feb299b00`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/lib/mcp/helpers_spec.spl
mirror: doc/06_spec/feature/lib/mcp/helpers_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/lib/mcp/helpers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/lib/mcp/helpers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/lib/mcp/helpers_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/lib/mcp/helpers_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provides brace helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/lib/mcp/helpers_spec.spl:128:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses integers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/lib/mcp/helpers_spec.spl:136:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calculates minimum' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
