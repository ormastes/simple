# Mcp T32 Json Specification

> Tests covering T32 MCP JSON Helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 Json Specification

## Scenarios

### T32 MCP JSON Helpers

#### wraps string in quotes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- wraps string in quotes
   - Expected: result equals `"hello"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps string in quotes")
val result = tjs("hello")
expect(result).to_equal("\"hello\"")
```

</details>

#### escapes quotes in string

- escapes quotes in string


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes quotes in string")
val result = tjs("say \"hi\"")
expect(result).to_contain("\\\"")
```

</details>

#### escapes newlines

- escapes newlines


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes newlines")
val result = tjs("line1\nline2")
expect(result).to_contain("\\n")
```

</details>

#### creates key-value pair

- creates key-value pair


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates key-value pair")
val result = tjp("name", tjs("test"))
expect(result).to_start_with("\"name\"")
expect(result).to_contain("\"test\"")
```

</details>

#### creates JSON object

- creates JSON object


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates JSON object")
val result = tjo1(tjp("key", tjs("val")))
expect(result).to_start_with("{")
expect(result).to_end_with("}")
```

</details>

#### parses initialize method with shared extractor behavior

- parses initialize method with shared extractor behavior
   - Expected: lsp_extract_field(json, "method") equals `initialize`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses initialize method with shared extractor behavior")
val json = "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"capabilities\":{},\"clientInfo\":{\"name\":\"probe\",\"version\":\"1.0\"}}}"
expect(lsp_extract_field(json, "method")).to_equal("initialize")
```

</details>

#### parses numeric id with shared extractor behavior

- parses numeric id with shared extractor behavior
   - Expected: lsp_extract_id(json) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses numeric id with shared extractor behavior")
val json = "{\"jsonrpc\":\"2.0\",\"id\":42,\"method\":\"initialize\"}"
expect(lsp_extract_id(json)).to_equal("42")
```

</details>

#### parses nested params fields with shared extractor behavior

- parses nested params fields with shared extractor behavior
   - Expected: lsp_extract_nested(json, "name") equals `cmm_parse`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses nested params fields with shared extractor behavior")
val json = "{\"method\":\"tools/call\",\"params\":{\"name\":\"cmm_parse\",\"arguments\":{\"source\":\"do main\"}}}"
expect(lsp_extract_nested(json, "name")).to_equal("cmm_parse")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_t32/mcp_t32_json_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 MCP JSON Helpers.
- T32 MCP JSON Helpers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `899539c0d4dd73b30fe06d06e8bfb2d26d9d3e37fd08d7d5112d6dbbed7c2098`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `899539c0d4dd73b30fe06d06e8bfb2d26d9d3e37fd08d7d5112d6dbbed7c2098`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `899539c0d4dd73b30fe06d06e8bfb2d26d9d3e37fd08d7d5112d6dbbed7c2098`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_t32/mcp_t32_json_spec.spl
mirror: doc/06_spec/unit/app/mcp_t32/mcp_t32_json_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_t32/mcp_t32_json_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_t32/mcp_t32_json_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_t32/mcp_t32_json_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps string in quotes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_json_spec.spl:120:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes quotes in string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_json_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes newlines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
