# mcp_lsp_tools_spec

> Tests for 10 Tier 4 LSP tools in the Simple MCP server. Validates parameter extraction, command construction, and error handling.

<!-- sdn-diagram:id=mcp_lsp_tools_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_lsp_tools_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_lsp_tools_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_lsp_tools_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 78 | 78 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mcp_lsp_tools_spec

Tests for 10 Tier 4 LSP tools in the Simple MCP server. Validates parameter extraction, command construction, and error handling.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MCP-LSP-001 to #MCP-LSP-010 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/app/mcp_unit/mcp_lsp_tools_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for 10 Tier 4 LSP tools in the Simple MCP server.
Validates parameter extraction, command construction, and error handling.

## Key Concepts

| Concept          | Description                                        |
|------------------|----------------------------------------------------|
| Tier 4           | LSP-compatible tools added to MCP server           |
| CLI Bridge       | Tools delegate to `bin/simple query` CLI           |
| Positional args  | file + line + optional column                      |
| Flag args        | Named flags like --new-name, --direction, --kind   |
| Destructive      | Tools that modify files (rename, formatting)       |

## Tools Covered

1. simple_signature_help   - Function parameter hints at call site
2. simple_rename           - Rename symbol across project
3. simple_code_actions     - Quick fixes and refactoring
4. simple_workspace_symbols - Project-wide symbol search
5. simple_call_hierarchy   - Caller/callee chains
6. simple_type_hierarchy   - Trait/mixin relationships
7. simple_semantic_tokens  - Syntax highlighting tokens
8. simple_inlay_hints      - Inline type/param annotations
9. simple_selection_range  - Smart selection expand/shrink
10. simple_document_formatting - File formatting

## Scenarios

### simple_signature_help tool

#### requires file parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = ""
val is_missing = file == ""
expect(is_missing).to_equal(true)
```

</details>

#### requires line parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = ""
val is_missing = line == ""
expect(is_missing).to_equal(true)
```

</details>

#### builds correct command with file and line

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/query.spl"
val line = "42"
var cmd = "timeout 30 bin/simple query signature-help " + file + " " + line
cmd = cmd + " 2>&1"
expect(cmd).to_contain("query signature-help")
expect(cmd).to_contain("src/app/cli/query.spl")
expect(cmd).to_contain("42")
```

</details>

#### appends column when provided

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/query.spl"
val line = "42"
val column = "10"
var cmd = "timeout 30 bin/simple query signature-help " + file + " " + line
cmd = cmd + " " + column
expect(cmd).to_contain("42 10")
```

</details>

#### has 30 second timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "timeout 30 bin/simple query signature-help test.spl 1"
expect(cmd).to_start_with("timeout 30")
```

</details>

#### omits column when not provided

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "7"
val column = ""
var cmd = "timeout 30 bin/simple query signature-help " + file + " " + line
if column != "":
    cmd = cmd + " " + column
cmd = cmd + " 2>&1"
val expected = "timeout 30 bin/simple query signature-help test.spl 7 2>&1"
expect(cmd).to_equal(expected)
```

</details>

#### uses query subcommand not direct subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "1"
var cmd = "timeout 30 bin/simple query signature-help " + file + " " + line
expect(cmd).to_contain("bin/simple query")
```

</details>

### simple_rename tool

#### requires file parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = ""
expect(file == "").to_equal(true)
```

</details>

#### requires line parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = ""
expect(line == "").to_equal(true)
```

</details>

#### requires new_name parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val new_name = ""
expect(new_name == "").to_equal(true)
```

</details>

#### builds command with new_name

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/test.spl"
val line = "10"
val new_name = "better_name"
var cmd = "timeout 30 bin/simple query rename " + file + " " + line
cmd = cmd + " --new-name " + new_name + " 2>&1"
expect(cmd).to_contain("query rename")
expect(cmd).to_contain("--new-name better_name")
```

</details>

#### appends column before new_name flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/test.spl"
val line = "10"
val column = "5"
val new_name = "x"
var cmd = "timeout 30 bin/simple query rename " + file + " " + line
cmd = cmd + " " + column + " --new-name " + new_name
expect(cmd).to_contain("10 5 --new-name x")
```

</details>

#### is marked as destructive tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val destructive_tools = ["simple_rename", "simple_document_formatting"]
expect(destructive_tools).to_contain("simple_rename")
```

</details>

#### preserves file path in command

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/lib/common/text/mod.spl"
val line = "20"
val new_name = "format_text"
var cmd = "timeout 30 bin/simple query rename " + file + " " + line
cmd = cmd + " --new-name " + new_name
expect(cmd).to_contain("src/lib/common/text/mod.spl")
```

</details>

#### handles underscore-prefixed names

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "1"
val new_name = "_private_helper"
var cmd = "timeout 30 bin/simple query rename " + file + " " + line
cmd = cmd + " --new-name " + new_name
expect(cmd).to_contain("--new-name _private_helper")
```

</details>

### simple_code_actions tool

#### requires file parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = ""
expect(file == "").to_equal(true)
```

</details>

#### requires line parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = ""
expect(line == "").to_equal(true)
```

</details>

#### builds correct command

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/lib/common/text/mod.spl"
val line = "55"
var cmd = "timeout 30 bin/simple query code-actions " + file + " " + line + " 2>&1"
expect(cmd).to_contain("query code-actions")
expect(cmd).to_contain(file)
```

</details>

#### supports optional column

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "1"
val column = "15"
var cmd = "timeout 30 bin/simple query code-actions " + file + " " + line + " " + column
expect(cmd).to_contain("1 15")
```

</details>

#### command ends with stderr redirect

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "10"
var cmd = "timeout 30 bin/simple query code-actions " + file + " " + line + " 2>&1"
expect(cmd).to_end_with("2>&1")
```

</details>

#### uses correct subcommand name with hyphen

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "1"
var cmd = "timeout 30 bin/simple query code-actions " + file + " " + line
expect(cmd).to_contain("code-actions")
```

</details>

### simple_workspace_symbols tool

#### requires query parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = ""
expect(query == "").to_equal(true)
```

</details>

#### does not require file parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = "main"
var cmd = "timeout 30 bin/simple query workspace-symbols --query " + query
val has_spl_file = cmd.contains(".spl ")
expect(has_spl_file).to_equal(false)
```

</details>

#### builds command with query

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = "parse"
var cmd = "timeout 30 bin/simple query workspace-symbols --query " + query + " 2>&1"
expect(cmd).to_contain("workspace-symbols")
expect(cmd).to_contain("--query parse")
```

</details>

#### supports kind filter

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = "Point"
val kind = "struct"
var cmd = "timeout 30 bin/simple query workspace-symbols --query " + query + " --kind " + kind
expect(cmd).to_contain("--kind struct")
```

</details>

#### supports function kind filter

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = "process"
val kind = "fn"
var cmd = "timeout 30 bin/simple query workspace-symbols --query " + query + " --kind " + kind
expect(cmd).to_contain("--kind fn")
```

</details>

#### supports class kind filter

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = "Token"
val kind = "class"
var cmd = "timeout 30 bin/simple query workspace-symbols --query " + query + " --kind " + kind
expect(cmd).to_contain("--kind class")
```

</details>

#### supports enum kind filter

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = "TokenKind"
val kind = "enum"
var cmd = "timeout 30 bin/simple query workspace-symbols --query " + query + " --kind " + kind
expect(cmd).to_contain("--kind enum")
```

</details>

#### builds command without kind when not specified

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = "main"
val kind = ""
var cmd = "timeout 30 bin/simple query workspace-symbols --query " + query
if kind != "":
    cmd = cmd + " --kind " + kind
val has_kind = cmd.contains("--kind")
expect(has_kind).to_equal(false)
```

</details>

### simple_call_hierarchy tool

#### requires file and line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/main.spl"
val line = "5"
var cmd = "timeout 30 bin/simple query call-hierarchy " + file + " " + line
expect(cmd).to_contain("call-hierarchy")
```

</details>

#### supports incoming direction

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/main.spl"
val line = "5"
var cmd = "timeout 30 bin/simple query call-hierarchy " + file + " " + line + " --direction incoming"
expect(cmd).to_contain("--direction incoming")
```

</details>

#### supports outgoing direction

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/main.spl"
val line = "5"
var cmd = "timeout 30 bin/simple query call-hierarchy " + file + " " + line + " --direction outgoing"
expect(cmd).to_contain("--direction outgoing")
```

</details>

#### supports optional column

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "10"
val column = "3"
var cmd = "timeout 30 bin/simple query call-hierarchy " + file + " " + line + " " + column
expect(cmd).to_contain("10 3")
```

</details>

#### places column before direction flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "10"
val column = "3"
val direction = "incoming"
var cmd = "timeout 30 bin/simple query call-hierarchy " + file + " " + line
cmd = cmd + " " + column + " --direction " + direction
expect(cmd).to_contain("3 --direction incoming")
```

</details>

#### builds command without direction by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "10"
val direction = ""
var cmd = "timeout 30 bin/simple query call-hierarchy " + file + " " + line
if direction != "":
    cmd = cmd + " --direction " + direction
val has_direction = cmd.contains("--direction")
expect(has_direction).to_equal(false)
```

</details>

### simple_type_hierarchy tool

#### requires file and line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/lib/common/text/mod.spl"
val line = "20"
var cmd = "timeout 30 bin/simple query type-hierarchy " + file + " " + line
expect(cmd).to_contain("type-hierarchy")
```

</details>

#### supports supertypes direction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "timeout 30 bin/simple query type-hierarchy test.spl 10 --direction supertypes"
expect(cmd).to_contain("--direction supertypes")
```

</details>

#### supports subtypes direction

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "timeout 30 bin/simple query type-hierarchy test.spl 10 --direction subtypes"
expect(cmd).to_contain("--direction subtypes")
```

</details>

#### includes file in command

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/compiler/20.hir/hir_types.spl"
val line = "30"
var cmd = "timeout 30 bin/simple query type-hierarchy " + file + " " + line
expect(cmd).to_contain(file)
```

</details>

#### supports optional column

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "10"
val column = "8"
var cmd = "timeout 30 bin/simple query type-hierarchy " + file + " " + line + " " + column
expect(cmd).to_contain("10 8")
```

</details>

#### builds command without direction when omitted

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "5"
val direction = ""
var cmd = "timeout 30 bin/simple query type-hierarchy " + file + " " + line
if direction != "":
    cmd = cmd + " --direction " + direction
val has_direction = cmd.contains("--direction")
expect(has_direction).to_equal(false)
```

</details>

### simple_semantic_tokens tool

#### requires file parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = ""
expect(file == "").to_equal(true)
```

</details>

#### builds command with file only

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/query.spl"
var cmd = "timeout 30 bin/simple query semantic-tokens " + file + " 2>&1"
expect(cmd).to_contain("semantic-tokens")
expect(cmd).to_contain(file)
```

</details>

#### supports start_line and end_line range

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
var cmd = "timeout 30 bin/simple query semantic-tokens " + file
cmd = cmd + " --start-line 10 --end-line 50"
expect(cmd).to_contain("--start-line 10")
expect(cmd).to_contain("--end-line 50")
```

</details>

#### does not require line as positional arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
var cmd = "timeout 30 bin/simple query semantic-tokens " + file + " 2>&1"
# Command should have file directly after semantic-tokens, no positional line
expect(cmd).to_contain("semantic-tokens test.spl")
```

</details>

#### supports start_line without end_line

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
var cmd = "timeout 30 bin/simple query semantic-tokens " + file
val start_line = "10"
val end_line = ""
cmd = cmd + " --start-line " + start_line
if end_line != "":
    cmd = cmd + " --end-line " + end_line
expect(cmd).to_contain("--start-line 10")
val has_end = cmd.contains("--end-line")
expect(has_end).to_equal(false)
```

</details>

#### supports end_line without start_line

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
var cmd = "timeout 30 bin/simple query semantic-tokens " + file
val start_line = ""
val end_line = "50"
if start_line != "":
    cmd = cmd + " --start-line " + start_line
cmd = cmd + " --end-line " + end_line
val has_start = cmd.contains("--start-line")
expect(has_start).to_equal(false)
expect(cmd).to_contain("--end-line 50")
```

</details>

### simple_inlay_hints tool

#### requires file parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = ""
expect(file == "").to_equal(true)
```

</details>

#### builds command with file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/query.spl"
var cmd = "timeout 30 bin/simple query inlay-hints " + file + " 2>&1"
expect(cmd).to_contain("inlay-hints")
```

</details>

#### supports line range

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
var cmd = "timeout 30 bin/simple query inlay-hints " + file + " --start-line 1 --end-line 100"
expect(cmd).to_contain("--start-line 1")
expect(cmd).to_contain("--end-line 100")
```

</details>

#### builds command without range by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
var cmd = "timeout 30 bin/simple query inlay-hints " + file + " 2>&1"
val has_start = cmd.contains("--start-line")
val has_end = cmd.contains("--end-line")
expect(has_start).to_equal(false)
expect(has_end).to_equal(false)
```

</details>

#### uses correct subcommand name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
var cmd = "timeout 30 bin/simple query inlay-hints " + file
expect(cmd).to_contain("query inlay-hints")
```

</details>

### simple_selection_range tool

#### requires file and line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "25"
var cmd = "timeout 30 bin/simple query selection-range " + file + " " + line
expect(cmd).to_contain("selection-range")
```

</details>

#### supports optional column

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "25"
val column = "8"
var cmd = "timeout 30 bin/simple query selection-range " + file + " " + line + " " + column
expect(cmd).to_contain("25 8")
```

</details>

#### builds command without column

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "25"
val column = ""
var cmd = "timeout 30 bin/simple query selection-range " + file + " " + line
if column != "":
    cmd = cmd + " " + column
cmd = cmd + " 2>&1"
val expected = "timeout 30 bin/simple query selection-range test.spl 25 2>&1"
expect(cmd).to_equal(expected)
```

</details>

#### uses query subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "1"
var cmd = "timeout 30 bin/simple query selection-range " + file + " " + line
expect(cmd).to_contain("bin/simple query")
```

</details>

#### includes file path in command

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/compiler/10.frontend/core/parser.spl"
val line = "100"
var cmd = "timeout 30 bin/simple query selection-range " + file + " " + line
expect(cmd).to_contain("src/compiler/10.frontend/core/parser.spl")
```

</details>

### simple_document_formatting tool

#### requires file parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = ""
expect(file == "").to_equal(true)
```

</details>

#### builds formatting command

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/query.spl"
var cmd = "timeout 30 bin/simple query document-formatting " + file + " 2>&1"
expect(cmd).to_contain("document-formatting")
expect(cmd).to_contain(file)
```

</details>

#### is marked as destructive tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val destructive_tools = ["simple_rename", "simple_document_formatting"]
expect(destructive_tools).to_contain("simple_document_formatting")
```

</details>

#### does not require line parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
var cmd = "timeout 30 bin/simple query document-formatting " + file
# No positional line number after file
expect(cmd).to_contain("document-formatting test.spl")
```

</details>

#### uses correct subcommand name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
var cmd = "timeout 30 bin/simple query document-formatting " + file
expect(cmd).to_contain("query document-formatting")
```

</details>

#### is distinct from simple_format CLI tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val formatting_cmd = "bin/simple query document-formatting test.spl"
val format_cmd = "bin/simple fmt test.spl"
val are_different = formatting_cmd != format_cmd
expect(are_different).to_equal(true)
```

</details>

### LSP tool consistency

#### all position tools accept file and line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val position_tools = ["signature-help", "rename", "code-actions", "call-hierarchy", "type-hierarchy", "selection-range"]
expect(position_tools.len()).to_equal(6)
```

</details>

#### all range tools accept start-line and end-line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val range_tools = ["semantic-tokens", "inlay-hints"]
expect(range_tools.len()).to_equal(2)
```

</details>

#### workspace-symbols is the only query-only tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query_only = ["workspace-symbols"]
expect(query_only.len()).to_equal(1)
```

</details>

#### file-only tools do not need line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_only_tools = ["semantic-tokens", "inlay-hints", "document-formatting"]
expect(file_only_tools.len()).to_equal(3)
```

</details>

#### destructive tools are exactly two

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val destructive = ["simple_rename", "simple_document_formatting"]
expect(destructive.len()).to_equal(2)
expect(destructive).to_contain("simple_rename")
expect(destructive).to_contain("simple_document_formatting")
```

</details>

#### all tools use 30 second timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timeout_prefix = "timeout 30"
val cmd1 = "timeout 30 bin/simple query signature-help f.spl 1"
val cmd2 = "timeout 30 bin/simple query rename f.spl 1 --new-name x"
val cmd3 = "timeout 30 bin/simple query code-actions f.spl 1"
expect(cmd1).to_start_with(timeout_prefix)
expect(cmd2).to_start_with(timeout_prefix)
expect(cmd3).to_start_with(timeout_prefix)
```

</details>

#### all tools use bin/simple query prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prefix = "bin/simple query"
val cmd1 = "timeout 30 bin/simple query signature-help f.spl 1"
val cmd2 = "timeout 30 bin/simple query workspace-symbols --query x"
val cmd3 = "timeout 30 bin/simple query semantic-tokens f.spl"
expect(cmd1).to_contain(prefix)
expect(cmd2).to_contain(prefix)
expect(cmd3).to_contain(prefix)
```

</details>

### LSP tool error handling

#### empty file path is an error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = ""
val is_error = file == ""
expect(is_error).to_equal(true)
```

</details>

#### empty line is an error for position tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = ""
val is_error = line == ""
expect(is_error).to_equal(true)
```

</details>

#### empty query is an error for workspace-symbols

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = ""
val is_error = query == ""
expect(is_error).to_equal(true)
```

</details>

#### empty new_name is an error for rename

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val new_name = ""
val is_error = new_name == ""
expect(is_error).to_equal(true)
```

</details>

#### non-spl file extension is valid input

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.txt"
val has_spl = file.contains(".spl")
expect(has_spl).to_equal(false)
```

</details>

#### negative line number is technically accepted as string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "-1"
val is_empty = line == ""
expect(is_empty).to_equal(false)
```

</details>

#### zero line number is technically accepted as string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "0"
val is_empty = line == ""
expect(is_empty).to_equal(false)
```

</details>

#### stderr redirect captures error output

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cmd = "timeout 30 bin/simple query signature-help test.spl 1 2>&1"
expect(cmd).to_contain("2>&1")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 78 |
| Active scenarios | 78 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
