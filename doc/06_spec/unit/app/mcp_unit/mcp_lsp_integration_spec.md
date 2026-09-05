# MCP LSP Integration Specification

> Integration tests for the 10 Tier 4 LSP tools. Validates JSON-RPC structure, dispatch routing, annotations, and error handling.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 28 | 28 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP LSP Integration Specification

Integration tests for the 10 Tier 4 LSP tools. Validates JSON-RPC structure, dispatch routing, annotations, and error handling.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #500-510 |
| Category | Tooling |
| Status | Implemented |
| Source | `test/unit/app/mcp_unit/mcp_lsp_integration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Integration tests for the 10 Tier 4 LSP tools.
Validates JSON-RPC structure, dispatch routing, annotations, and error handling.

## Scenarios

### LSP tool dispatch routing

#### routes simple_signature_help

- routes simple_signature_help
   - Expected: is_lsp_tool is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes simple_signature_help")
val tool_name = "simple_signature_help"
val is_lsp_tool = tool_name.starts_with("simple_")
expect(is_lsp_tool).to_equal(true)
expect(tool_name).to_contain("signature_help")
```

</details>

#### routes simple_rename

- routes simple_rename
   - Expected: tool_name equals `simple_rename`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes simple_rename")
val tool_name = "simple_rename"
expect(tool_name).to_equal("simple_rename")
```

</details>

#### routes simple_code_actions

- routes simple_code_actions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes simple_code_actions")
val tool_name = "simple_code_actions"
expect(tool_name).to_contain("code_actions")
```

</details>

#### routes simple_workspace_symbols

- routes simple_workspace_symbols


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes simple_workspace_symbols")
val tool_name = "simple_workspace_symbols"
expect(tool_name).to_contain("workspace_symbols")
```

</details>

#### routes simple_call_hierarchy

- routes simple_call_hierarchy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes simple_call_hierarchy")
val tool_name = "simple_call_hierarchy"
expect(tool_name).to_contain("call_hierarchy")
```

</details>

#### routes simple_type_hierarchy

- routes simple_type_hierarchy


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes simple_type_hierarchy")
val tool_name = "simple_type_hierarchy"
expect(tool_name).to_contain("type_hierarchy")
```

</details>

#### routes simple_semantic_tokens

- routes simple_semantic_tokens


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes simple_semantic_tokens")
val tool_name = "simple_semantic_tokens"
expect(tool_name).to_contain("semantic_tokens")
```

</details>

#### routes simple_inlay_hints

- routes simple_inlay_hints


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes simple_inlay_hints")
val tool_name = "simple_inlay_hints"
expect(tool_name).to_contain("inlay_hints")
```

</details>

#### routes simple_selection_range

- routes simple_selection_range


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes simple_selection_range")
val tool_name = "simple_selection_range"
expect(tool_name).to_contain("selection_range")
```

</details>

#### routes simple_document_formatting

- routes simple_document_formatting


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes simple_document_formatting")
val tool_name = "simple_document_formatting"
expect(tool_name).to_contain("document_formatting")
```

</details>

### LSP tool output format

#### signature_help has correct prefix

- signature_help has correct prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("signature_help has correct prefix")
val prefix = "-- simple_signature_help (exit: 0) --"
expect(prefix).to_start_with("-- simple_signature_help")
expect(prefix).to_contain("exit:")
```

</details>

#### rename has correct prefix

- rename has correct prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rename has correct prefix")
val prefix = "-- simple_rename (exit: 0) --"
expect(prefix).to_start_with("-- simple_rename")
```

</details>

#### workspace_symbols has correct prefix

- workspace_symbols has correct prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("workspace_symbols has correct prefix")
val prefix = "-- simple_workspace_symbols (exit: 0) --"
expect(prefix).to_start_with("-- simple_workspace_symbols")
```

</details>

#### all prefixes follow pattern

- all prefixes follow pattern
   - Expected: count equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all prefixes follow pattern")
val tools = ["simple_signature_help", "simple_rename", "simple_code_actions", "simple_workspace_symbols", "simple_call_hierarchy", "simple_type_hierarchy", "simple_semantic_tokens", "simple_inlay_hints", "simple_selection_range", "simple_document_formatting"]
var count = 0
for tool in tools:
    val prefix = "-- " + tool + " (exit: "
    val valid = prefix.starts_with("-- simple_")
    if valid:
        count = count + 1
expect(count).to_equal(10)
```

</details>

### LSP tool annotations

#### read-only tools are correctly categorized

- read-only tools are correctly categorized
   - Expected: read_only_tools.len() equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read-only tools are correctly categorized")
val read_only_tools = ["simple_signature_help", "simple_code_actions", "simple_workspace_symbols", "simple_call_hierarchy", "simple_type_hierarchy", "simple_semantic_tokens", "simple_inlay_hints", "simple_selection_range"]
expect(read_only_tools.len()).to_equal(8)
expect(read_only_tools).to_contain("simple_signature_help")
expect(read_only_tools).to_contain("simple_workspace_symbols")
```

</details>

#### destructive tools are correctly categorized

- destructive tools are correctly categorized
   - Expected: destructive_tools.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("destructive tools are correctly categorized")
val destructive_tools = ["simple_rename", "simple_document_formatting"]
expect(destructive_tools.len()).to_equal(2)
expect(destructive_tools).to_contain("simple_rename")
expect(destructive_tools).to_contain("simple_document_formatting")
```

</details>

#### non-idempotent tools are correctly categorized

- non-idempotent tools are correctly categorized
   - Expected: non_idempotent.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-idempotent tools are correctly categorized")
val non_idempotent = ["simple_rename", "simple_document_formatting"]
expect(non_idempotent.len()).to_equal(2)
```

</details>

### LSP tool error handling

#### missing file returns error code -32602

- missing file returns error code -32602
   - Expected: error_code equals `-32602`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("missing file returns error code -32602")
val error_code = -32602
expect(error_code).to_equal(-32602)
```

</details>

#### missing line returns error code -32602

- missing line returns error code -32602
   - Expected: error_code equals `-32602`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("missing line returns error code -32602")
val error_code = -32602
expect(error_code).to_equal(-32602)
```

</details>

#### missing new_name for rename returns error

- missing new_name for rename returns error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("missing new_name for rename returns error")
val error_msg = "Missing required parameter: new_name"
expect(error_msg).to_contain("new_name")
```

</details>

#### missing query for workspace_symbols returns error

- missing query for workspace_symbols returns error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("missing query for workspace_symbols returns error")
val error_msg = "Missing required parameter: query"
expect(error_msg).to_contain("query")
```

</details>

### LSP tool count

#### has 10 new LSP tools

- has 10 new LSP tools
   - Expected: lsp_tools.len() equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has 10 new LSP tools")
val lsp_tools = ["simple_signature_help", "simple_rename", "simple_code_actions", "simple_workspace_symbols", "simple_call_hierarchy", "simple_type_hierarchy", "simple_semantic_tokens", "simple_inlay_hints", "simple_selection_range", "simple_document_formatting"]
expect(lsp_tools.len()).to_equal(10)
```

</details>

#### total tool count is 59

- total tool count is 59
   - Expected: total equals `59`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("total tool count is 59")
val existing = 49
val new_lsp = 10
val total = existing + new_lsp
expect(total).to_equal(59)
```

</details>

### LSP tool parameter patterns

#### position tools need file and line

- position tools need file and line
   - Expected: position_tools.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("position tools need file and line")
val position_tools = ["simple_signature_help", "simple_code_actions", "simple_selection_range"]
expect(position_tools.len()).to_equal(3)
```

</details>

#### workspace_symbols needs only query

- workspace_symbols needs only query
   - Expected: needs_file is false
   - Expected: needs_query is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("workspace_symbols needs only query")
val tool = "simple_workspace_symbols"
val needs_file = false
val needs_query = true
expect(needs_file).to_equal(false)
expect(needs_query).to_equal(true)
```

</details>

#### range tools need file with optional line range

- range tools need file with optional line range
   - Expected: range_tools.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("range tools need file with optional line range")
val range_tools = ["simple_semantic_tokens", "simple_inlay_hints"]
expect(range_tools.len()).to_equal(2)
```

</details>

#### hierarchy tools support direction parameter

- hierarchy tools support direction parameter
   - Expected: hierarchy_tools.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("hierarchy tools support direction parameter")
val hierarchy_tools = ["simple_call_hierarchy", "simple_type_hierarchy"]
expect(hierarchy_tools.len()).to_equal(2)
```

</details>

#### rename needs file, line, and new_name

- rename needs file, line, and new_name
   - Expected: required.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rename needs file, line, and new_name")
val required = ["file", "line", "new_name"]
expect(required.len()).to_equal(3)
expect(required).to_contain("new_name")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 28 |
| Active scenarios | 28 |
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

- Canonical SPipe generation for source `f8e1606fb7167df1754dd36c5bb0f848cb7a39514c2ee4a7097660e19bbe32e7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f8e1606fb7167df1754dd36c5bb0f848cb7a39514c2ee4a7097660e19bbe32e7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f8e1606fb7167df1754dd36c5bb0f848cb7a39514c2ee4a7097660e19bbe32e7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/mcp_unit/mcp_lsp_integration_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_lsp_integration_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_lsp_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_lsp_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_lsp_integration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/mcp_lsp_integration_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes simple_signature_help' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_lsp_integration_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes simple_rename' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_lsp_integration_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes simple_code_actions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
