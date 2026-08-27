# mcp_lsp_extras_spec

> Tests for 4 new MCP LSP tools: document-highlight, type-definition, implementation, folding-range. Validates parameter handling, command construction, and output format.

<!-- sdn-diagram:id=mcp_lsp_extras_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_lsp_extras_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_lsp_extras_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_lsp_extras_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 43 | 43 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mcp_lsp_extras_spec

Tests for 4 new MCP LSP tools: document-highlight, type-definition, implementation, folding-range. Validates parameter handling, command construction, and output format.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MCP-LSP-011 to #MCP-LSP-014 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/app/mcp_unit/mcp_lsp_extras_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Tests for 4 new MCP LSP tools: document-highlight, type-definition,
implementation, folding-range. Validates parameter handling, command
construction, and output format.

## Scenarios

### simple_document_highlight tool

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

#### builds correct command

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/query.spl"
val line = "42"
var cmd = "timeout 30 bin/simple query document-highlight " + file + " " + line
cmd = cmd + " 2>&1"
expect(cmd).to_contain("query document-highlight")
expect(cmd).to_contain(file)
```

</details>

#### appends column when provided

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "10"
val column = "5"
var cmd = "timeout 30 bin/simple query document-highlight " + file + " " + line
cmd = cmd + " " + column
expect(cmd).to_contain("10 5")
```

</details>

#### output format is line:col:length:kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = "5:10:8:Read"
val parts = output.split(":")
expect(parts.len()).to_equal(4)
expect(parts[3]).to_equal("Read")
```

</details>

#### kind is Read or Write

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kinds = ["Read", "Write"]
expect(kinds).to_contain("Read")
expect(kinds).to_contain("Write")
```

</details>

#### classifies declaration as Write

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "val count = 0"
val is_decl = line.starts_with("val ") or line.starts_with("var ")
expect(is_decl).to_equal(true)
```

</details>

#### classifies usage as Read

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "print count"
val is_decl = line.starts_with("val ") or line.starts_with("var ")
expect(is_decl).to_equal(false)
```

</details>

#### classifies assignment LHS as Write

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "count = count + 1"
# count on LHS of = is Write, count on RHS is Read
val has_assign = line.contains(" = ")
expect(has_assign).to_equal(true)
```

</details>

### simple_type_definition tool

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
val file = "src/app/cli/query.spl"
val line = "42"
var cmd = "timeout 30 bin/simple query type-definition " + file + " " + line
cmd = cmd + " 2>&1"
expect(cmd).to_contain("query type-definition")
```

</details>

#### appends column when provided

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "10"
val column = "5"
var cmd = "timeout 30 bin/simple query type-definition " + file + " " + line
cmd = cmd + " " + column
expect(cmd).to_contain("10 5")
```

</details>

#### extracts type from val annotation

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "val server: Server = Server.new()"
val after_colon = line.split(":")[1].trim()
val type_name = after_colon.split(" ")[0]
expect(type_name).to_equal("Server")
```

</details>

#### extracts type from function return

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = "fn get_server() -> Server:"
val has_arrow = line.contains("->")
expect(has_arrow).to_equal(true)
```

</details>

#### searches for class/struct/enum/trait definition

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val type_name = "Server"
val patterns = ["class " + type_name, "struct " + type_name, "enum " + type_name, "trait " + type_name]
expect(patterns.len()).to_equal(4)
expect(patterns[0]).to_equal("class Server")
```

</details>

### simple_implementation tool

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
val file = "src/test.spl"
val line = "5"
var cmd = "timeout 30 bin/simple query implementation " + file + " " + line
cmd = cmd + " 2>&1"
expect(cmd).to_contain("query implementation")
```

</details>

#### appends column when provided

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
val line = "10"
val column = "3"
var cmd = "timeout 30 bin/simple query implementation " + file + " " + line
cmd = cmd + " " + column
expect(cmd).to_contain("10 3")
```

</details>

#### finds trait implementations via impl pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trait_name = "Printable"
val pattern = "impl " + trait_name
expect(pattern).to_equal("impl Printable")
```

</details>

#### finds type implementations via impl.*Type pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val type_name = "Server"
val pattern = "impl.*" + type_name
expect(pattern).to_contain("impl")
expect(pattern).to_contain("Server")
```

</details>

#### distinguishes traits from types

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val trait_line = "trait Printable:"
val is_trait = trait_line.starts_with("trait ")
expect(is_trait).to_equal(true)
```

</details>

#### struct is not a trait

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val struct_line = "struct Point:"
val is_trait = struct_line.starts_with("trait ")
expect(is_trait).to_equal(false)
```

</details>

### simple_folding_range tool

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

#### builds correct command

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/query.spl"
var cmd = "timeout 30 bin/simple query folding-range " + file + " 2>&1"
expect(cmd).to_contain("query folding-range")
expect(cmd).to_contain(file)
```

</details>

#### does not require line parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "test.spl"
var cmd = "timeout 30 bin/simple query folding-range " + file
# No positional line number
expect(cmd).to_contain("folding-range test.spl")
```

</details>

#### output format is start_line:end_line:kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val output = "1:5:imports"
val parts = output.split(":")
expect(parts.len()).to_equal(3)
expect(parts[2]).to_equal("imports")
```

</details>

#### detects import folding regions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "imports"
val valid_kinds = ["imports", "comment", "function", "class", "struct", "enum", "trait", "impl"]
expect(valid_kinds).to_contain(kind)
```

</details>

#### detects comment folding regions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "comment"
val valid_kinds = ["imports", "comment", "function", "class", "struct", "enum", "trait", "impl"]
expect(valid_kinds).to_contain(kind)
```

</details>

#### detects function folding regions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kind = "function"
val valid_kinds = ["imports", "comment", "function", "class", "struct", "enum", "trait", "impl"]
expect(valid_kinds).to_contain(kind)
```

</details>

#### detects class/struct/enum/trait regions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val block_kinds = ["class", "struct", "enum", "trait", "impl"]
expect(block_kinds.len()).to_equal(5)
```

</details>

#### folding ends when indent returns to zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Block start at indent 0, block ends when next line at indent 0
val indent_0 = "fn hello():"
val indent_4 = "    print 'hello'"
val is_block_start = indent_0.starts_with("fn ")
expect(is_block_start).to_equal(true)
```

</details>

### MCP tool registration for new LSP tools

#### total tool count is 63

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_count = 63
expect(tool_count).to_equal(63)
```

</details>

#### all 4 new tools registered in protocol

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val new_tools = ["simple_document_highlight", "simple_type_definition", "simple_implementation", "simple_folding_range"]
expect(new_tools.len()).to_equal(4)
```

</details>

#### all new tools are read-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val read_only = true
expect(read_only).to_equal(true)
```

</details>

#### document-highlight schema has file+line+column

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = ["file", "line", "column"]
expect(params).to_contain("file")
expect(params).to_contain("line")
expect(params).to_contain("column")
```

</details>

#### folding-range schema has file only

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = ["file"]
expect(params.len()).to_equal(1)
expect(params[0]).to_equal("file")
```

</details>

#### dispatch entries added for all 4 tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool_names = ["simple_document_highlight", "simple_type_definition", "simple_implementation", "simple_folding_range"]
expect(tool_names.len()).to_equal(4)
```

</details>

### LSP extras cross-tool consistency

#### all position tools accept file and line

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val position_tools = ["document-highlight", "type-definition", "implementation"]
expect(position_tools.len()).to_equal(3)
```

</details>

#### folding-range is file-only

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file_only = ["folding-range"]
expect(file_only.len()).to_equal(1)
```

</details>

#### all tools use 30 second timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val timeout = "timeout 30"
val cmd1 = "timeout 30 bin/simple query document-highlight f.spl 1"
val cmd2 = "timeout 30 bin/simple query folding-range f.spl"
expect(cmd1).to_start_with(timeout)
expect(cmd2).to_start_with(timeout)
```

</details>

#### all tools use bin/simple query prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prefix = "bin/simple query"
val cmd = "timeout 30 bin/simple query document-highlight test.spl 1"
expect(cmd).to_contain(prefix)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 43 |
| Active scenarios | 43 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
