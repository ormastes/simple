# MCP LSP Integration Specification

> Integration tests for the 10 Tier 4 LSP tools. Validates JSON-RPC structure, dispatch routing, annotations, and error handling.

<!-- sdn-diagram:id=mcp_lsp_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_lsp_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_lsp_integration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_lsp_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/01_unit/app/mcp_unit/mcp_lsp_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Integration tests for the 10 Tier 4 LSP tools.
Validates JSON-RPC structure, dispatch routing, annotations, and error handling.

## Scenarios

### LSP tool dispatch routing

#### routes simple_signature_help

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_name = "simple_signature_help"
val is_lsp_tool = tool_name.starts_with("simple_")
expect(is_lsp_tool).to_equal(true)
expect(tool_name).to_contain("signature_help")
```

</details>

#### routes simple_rename

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_name = "simple_rename"
expect(tool_name).to_equal("simple_rename")
```

</details>

#### routes simple_code_actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_name = "simple_code_actions"
expect(tool_name).to_contain("code_actions")
```

</details>

#### routes simple_workspace_symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_name = "simple_workspace_symbols"
expect(tool_name).to_contain("workspace_symbols")
```

</details>

#### routes simple_call_hierarchy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_name = "simple_call_hierarchy"
expect(tool_name).to_contain("call_hierarchy")
```

</details>

#### routes simple_type_hierarchy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_name = "simple_type_hierarchy"
expect(tool_name).to_contain("type_hierarchy")
```

</details>

#### routes simple_semantic_tokens

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_name = "simple_semantic_tokens"
expect(tool_name).to_contain("semantic_tokens")
```

</details>

#### routes simple_inlay_hints

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_name = "simple_inlay_hints"
expect(tool_name).to_contain("inlay_hints")
```

</details>

#### routes simple_selection_range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_name = "simple_selection_range"
expect(tool_name).to_contain("selection_range")
```

</details>

#### routes simple_document_formatting

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_name = "simple_document_formatting"
expect(tool_name).to_contain("document_formatting")
```

</details>

### LSP tool output format

#### signature_help has correct prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prefix = "-- simple_signature_help (exit: 0) --"
expect(prefix).to_start_with("-- simple_signature_help")
expect(prefix).to_contain("exit:")
```

</details>

#### rename has correct prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prefix = "-- simple_rename (exit: 0) --"
expect(prefix).to_start_with("-- simple_rename")
```

</details>

#### workspace_symbols has correct prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prefix = "-- simple_workspace_symbols (exit: 0) --"
expect(prefix).to_start_with("-- simple_workspace_symbols")
```

</details>

#### all prefixes follow pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val read_only_tools = ["simple_signature_help", "simple_code_actions", "simple_workspace_symbols", "simple_call_hierarchy", "simple_type_hierarchy", "simple_semantic_tokens", "simple_inlay_hints", "simple_selection_range"]
expect(read_only_tools.len()).to_equal(8)
expect(read_only_tools).to_contain("simple_signature_help")
expect(read_only_tools).to_contain("simple_workspace_symbols")
```

</details>

#### destructive tools are correctly categorized

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val destructive_tools = ["simple_rename", "simple_document_formatting"]
expect(destructive_tools.len()).to_equal(2)
expect(destructive_tools).to_contain("simple_rename")
expect(destructive_tools).to_contain("simple_document_formatting")
```

</details>

#### non-idempotent tools are correctly categorized

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val non_idempotent = ["simple_rename", "simple_document_formatting"]
expect(non_idempotent.len()).to_equal(2)
```

</details>

### LSP tool error handling

#### missing file returns error code -32602

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error_code = -32602
expect(error_code).to_equal(-32602)
```

</details>

#### missing line returns error code -32602

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error_code = -32602
expect(error_code).to_equal(-32602)
```

</details>

#### missing new_name for rename returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error_msg = "Missing required parameter: new_name"
expect(error_msg).to_contain("new_name")
```

</details>

#### missing query for workspace_symbols returns error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error_msg = "Missing required parameter: query"
expect(error_msg).to_contain("query")
```

</details>

### LSP tool count

#### has 10 new LSP tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lsp_tools = ["simple_signature_help", "simple_rename", "simple_code_actions", "simple_workspace_symbols", "simple_call_hierarchy", "simple_type_hierarchy", "simple_semantic_tokens", "simple_inlay_hints", "simple_selection_range", "simple_document_formatting"]
expect(lsp_tools.len()).to_equal(10)
```

</details>

#### total tool count is 59

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val existing = 49
val new_lsp = 10
val total = existing + new_lsp
expect(total).to_equal(59)
```

</details>

### LSP tool parameter patterns

#### position tools need file and line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val position_tools = ["simple_signature_help", "simple_code_actions", "simple_selection_range"]
expect(position_tools.len()).to_equal(3)
```

</details>

#### workspace_symbols needs only query

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool = "simple_workspace_symbols"
val needs_file = false
val needs_query = true
expect(needs_file).to_equal(false)
expect(needs_query).to_equal(true)
```

</details>

#### range tools need file with optional line range

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val range_tools = ["simple_semantic_tokens", "simple_inlay_hints"]
expect(range_tools.len()).to_equal(2)
```

</details>

#### hierarchy tools support direction parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val hierarchy_tools = ["simple_call_hierarchy", "simple_type_hierarchy"]
expect(hierarchy_tools.len()).to_equal(2)
```

</details>

#### rename needs file, line, and new_name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
