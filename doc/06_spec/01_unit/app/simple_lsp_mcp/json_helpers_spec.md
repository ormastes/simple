# Json Helpers Specification

> Tests covering Simple LSP MCP native JSON extraction.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Json Helpers Specification

## Scenarios

### Simple LSP MCP native JSON extraction

#### extracts the tool name from a standard tools/call request

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts the tool name from a standard tools/call request
   - Expected: extract_field(request, "name") equals `lsp_symbols`
   - Expected: extract_field(request, "file") equals `src/app/simple_lsp_mcp/main.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts the tool name from a standard tools/call request")
val request = "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"tools/call\",\"params\":{\"name\":\"lsp_symbols\",\"arguments\":{\"file\":\"src/app/simple_lsp_mcp/main.spl\"}}}"
expect(extract_field(request, "name")).to_equal("lsp_symbols")
expect(extract_field(request, "file")).to_equal("src/app/simple_lsp_mcp/main.spl")
```

</details>

#### preserves numeric and string request identifiers

- preserves numeric and string request identifiers
   - Expected: extract_id("{\"jsonrpc\":\"2.0\",\"id\":17}") equals `17`
   - Expected: extract_id("{\"jsonrpc\":\"2.0\",\"id\":23}") equals `23`
   - Expected: extract_id("{\"jsonrpc\":\"2.0\",\"id\":\"request-alpha\"}") equals `"request-alpha"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves numeric and string request identifiers")
expect(extract_id("{\"jsonrpc\":\"2.0\",\"id\":17}")).to_equal("17")
expect(extract_id("{\"jsonrpc\":\"2.0\",\"id\":23}")).to_equal("23")
expect(extract_id("{\"jsonrpc\":\"2.0\",\"id\":\"request-alpha\"}")).to_equal("\"request-alpha\"")
```

</details>

#### escapes tool result text exactly once on the wire

- escapes tool result text exactly once on the wire
   - Expected: make_tool_result("1", "[{\"name\":\"log_options_help\"}]") equals `{"jsonrpc":"2.0","id":1,"result":{"content":[{"type":"text","text":"[{\\"name... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes tool result text exactly once on the wire")
expect(make_tool_result("1", "[{\"name\":\"log_options_help\"}]")).to_equal("{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":{\"content\":[{\"type\":\"text\",\"text\":\"[{\\\"name\\\":\\\"log_options_help\\\"}]\"}]}" + "}")
```

</details>

#### escapes error messages exactly once on the wire

- escapes error messages exactly once on the wire
   - Expected: jsonrpc_error("2", -32000, "bad \"quote\"") equals `{"jsonrpc":"2.0","id":2,"error":{"code":-32000,"message":"bad \\"quote\\""}}"... (full value in folded executable source)`
   - Expected: make_tool_error("3", "bad \"quote\"") equals `{"jsonrpc":"2.0","id":3,"result":{"content":[{"type":"text","text":"bad \\"qu... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes error messages exactly once on the wire")
expect(jsonrpc_error("2", -32000, "bad \"quote\"")).to_equal("{\"jsonrpc\":\"2.0\",\"id\":2,\"error\":{\"code\":-32000,\"message\":\"bad \\\"quote\\\"\"}}" + "}")
expect(make_tool_error("3", "bad \"quote\"")).to_equal("{\"jsonrpc\":\"2.0\",\"id\":3,\"result\":{\"content\":[{\"type\":\"text\",\"text\":\"bad \\\"quote\\\"\"}],\"isError\":true}" + "}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/simple_lsp_mcp/json_helpers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Simple LSP MCP native JSON extraction.
- Simple LSP MCP native JSON extraction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cf5b5b0e1a6b0b9f83068b10964c83b2b8d7b625cb569cc7ba64e955875c6237`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cf5b5b0e1a6b0b9f83068b10964c83b2b8d7b625cb569cc7ba64e955875c6237`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cf5b5b0e1a6b0b9f83068b10964c83b2b8d7b625cb569cc7ba64e955875c6237`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/simple_lsp_mcp/json_helpers_spec.spl
mirror: doc/06_spec/01_unit/app/simple_lsp_mcp/json_helpers_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/simple_lsp_mcp/json_helpers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/simple_lsp_mcp/json_helpers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/simple_lsp_mcp/json_helpers_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts the tool name from a standard tools/call request' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/simple_lsp_mcp/json_helpers_spec.spl:21:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves numeric and string request identifiers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/simple_lsp_mcp/json_helpers_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes tool result text exactly once on the wire' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
