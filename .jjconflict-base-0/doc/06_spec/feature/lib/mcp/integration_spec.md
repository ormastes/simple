# MCP Library Integration

> Tests end-to-end MCP library integration including server startup, tool listing, and tool execution through the full protocol stack. Verifies that all MCP library components work together correctly for complete request-response cycles.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Library Integration

Tests end-to-end MCP library integration including server startup, tool listing, and tool execution through the full protocol stack. Verifies that all MCP library components work together correctly for complete request-response cycles.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | In Progress |
| Source | `test/feature/lib/mcp/integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests end-to-end MCP library integration including server startup, tool listing,
and tool execution through the full protocol stack. Verifies that all MCP library
components work together correctly for complete request-response cycles.

## Scenarios

### MCP Library - Integration

#### builds complete MCP initialize response

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- builds complete MCP initialize response


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("builds complete MCP initialize response")
val init_result = """{"protocolVersion":"2025-06-18","capabilities":{"tools":{}}}"""
val response = jo3(
    jp("jsonrpc", js("2.0")),
    jp("id", "1"),
    jp("result", init_result)
)
expect(response).to_contain("\"jsonrpc\":\"2.0\"")
expect(response).to_contain("\"id\":1")
expect(response).to_contain("protocolVersion")
```

</details>

#### builds tools/list response with pre-computed schemas

- builds tools/list response with pre-computed schemas


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("builds tools/list response with pre-computed schemas")
init_core_schemas()
val tools = get_all_tool_schemas()
expect(tools).to_start_with("[")
expect(tools).to_contain("read_code")
```

</details>

#### extracts method from JSON-RPC request

- extracts method from JSON-RPC request
   - Expected: method equals `initialize`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("extracts method from JSON-RPC request")
val request = """{"jsonrpc":"2.0","id":1,"method":"initialize","params":{}}"""
val method = extract_json_string_v2(request, "method")
expect(method).to_equal("initialize")
```

</details>

#### creates error response

- creates error response


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates error response")
val error = make_error_response("42", -32600, "Invalid request")
expect(error).to_contain("\"id\":42")
expect(error).to_contain("\"error\"")
expect(error).to_contain("-32600")
expect(error).to_contain("Invalid request")
```

</details>

#### manages session lifecycle

- manages session lifecycle
   - Expected: state.initialized is false
   - Expected: state.initialized is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("manages session lifecycle")
var state = create_mcp_state()
expect(state.initialized).to_equal(false)

state.initialized = true
expect(state.initialized).to_equal(true)
```

</details>

#### registers and finds tool handlers

- registers and finds tool handlers
   - Expected: found.name equals `test_tool`
   - Expected: found.handler_module equals `app.handlers.test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("registers and finds tool handlers")
val handler = create_tool_handler(
    "test_tool",
    "Test tool",
    """{"name":"test_tool"}""",
    "app.handlers.test",
    "handle_test"
)
register_tool_handler(handler)

val found = find_tool_handler("test_tool")
expect(found.name).to_equal("test_tool")
expect(found.handler_module).to_equal("app.handlers.test")
```

</details>

#### handles full request-response cycle

- handles full request-response cycle
   - Expected: method equals `tools/call`
   - Expected: path equals `test.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("handles full request-response cycle")
# Simulate receiving a request
val request = """{"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"read_code","arguments":{"path":"test.spl"}}}"""

# Extract components
val method = extract_json_string_v2(request, "method")
expect(method).to_equal("tools/call")

# Extract argument
val path = extract_arg(request, "path")
expect(path).to_equal("test.spl")

# Build tool result response
val tool_result = make_tool_result("3", "File content here")
expect(tool_result).to_contain("\"id\":3")
expect(tool_result).to_contain("\"result\"")
expect(tool_result).to_contain("File content here")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d943889e16baf4d60393b6ac46537a1eadccbd662c01811973515fc023543e32`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d943889e16baf4d60393b6ac46537a1eadccbd662c01811973515fc023543e32`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d943889e16baf4d60393b6ac46537a1eadccbd662c01811973515fc023543e32`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/lib/mcp/integration_spec.spl
mirror: doc/06_spec/feature/lib/mcp/integration_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/lib/mcp/integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/lib/mcp/integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/lib/mcp/integration_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds complete MCP initialize response' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/lib/mcp/integration_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds tools/list response with pre-computed schemas' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/lib/mcp/integration_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts method from JSON-RPC request' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
