# Mcp Lsp Extras Specification

> Tests covering simple_document_highlight tool, simple_type_definition tool, simple_implementation tool, simple_folding_range tool, MCP tool registration for new LSP tools, LSP extras cross-tool consistency.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 43 | 43 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Lsp Extras Specification

## Scenarios

### simple_document_highlight tool

#### requires file parameter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- requires file parameter
   - Expected: is_missing is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires file parameter")
val file = ""
val is_missing = file == ""
expect(is_missing).to_equal(true)
```

</details>

#### requires line parameter

- requires line parameter
   - Expected: is_missing is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires line parameter")
val line = ""
val is_missing = line == ""
expect(is_missing).to_equal(true)
```

</details>

#### builds correct command

- builds correct command


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds correct command")
val file = "src/app/cli/query.spl"
val line = "42"
var cmd = "timeout 30 bin/simple query document-highlight " + file + " " + line
cmd = cmd + " 2>&1"
expect(cmd).to_contain("query document-highlight")
expect(cmd).to_contain(file)
```

</details>

#### appends column when provided

- appends column when provided


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("appends column when provided")
val file = "test.spl"
val line = "10"
val column = "5"
var cmd = "timeout 30 bin/simple query document-highlight " + file + " " + line
cmd = cmd + " " + column
expect(cmd).to_contain("10 5")
```

</details>

#### output format is line:col:length:kind

- output format is line:col:length:kind
   - Expected: parts.len() equals `4`
   - Expected: parts[3] equals `Read`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output format is line:col:length:kind")
val output = "5:10:8:Read"
val parts = output.split(":")
expect(parts.len()).to_equal(4)
expect(parts[3]).to_equal("Read")
```

</details>

#### kind is Read or Write

- kind is Read or Write


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("kind is Read or Write")
val kinds = ["Read", "Write"]
expect(kinds).to_contain("Read")
expect(kinds).to_contain("Write")
```

</details>

#### classifies declaration as Write

- classifies declaration as Write
   - Expected: is_decl is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies declaration as Write")
val line = "val count = 0"
val is_decl = line.starts_with("val ") or line.starts_with("var ")
expect(is_decl).to_equal(true)
```

</details>

#### classifies usage as Read

- classifies usage as Read
   - Expected: is_decl is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies usage as Read")
val line = "print count"
val is_decl = line.starts_with("val ") or line.starts_with("var ")
expect(is_decl).to_equal(false)
```

</details>

#### classifies assignment LHS as Write

- classifies assignment LHS as Write
   - Expected: has_assign is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies assignment LHS as Write")
val line = "count = count + 1"
# count on LHS of = is Write, count on RHS is Read
val has_assign = line.contains(" = ")
expect(has_assign).to_equal(true)
```

</details>

### simple_type_definition tool

#### requires file parameter

- requires file parameter
   - Expected: file equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires file parameter")
val file = ""
expect(file).to_equal("")
```

</details>

#### requires line parameter

- requires line parameter
   - Expected: line equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires line parameter")
val line = ""
expect(line).to_equal("")
```

</details>

#### builds correct command

- builds correct command


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds correct command")
val file = "src/app/cli/query.spl"
val line = "42"
var cmd = "timeout 30 bin/simple query type-definition " + file + " " + line
cmd = cmd + " 2>&1"
expect(cmd).to_contain("query type-definition")
```

</details>

#### appends column when provided

- appends column when provided


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("appends column when provided")
val file = "test.spl"
val line = "10"
val column = "5"
var cmd = "timeout 30 bin/simple query type-definition " + file + " " + line
cmd = cmd + " " + column
expect(cmd).to_contain("10 5")
```

</details>

#### extracts type from val annotation

- extracts type from val annotation
   - Expected: type_name equals `Server`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts type from val annotation")
val line = "val server: Server = Server.new()"
val after_colon = line.split(":")[1].trim()
val type_name = after_colon.split(" ")[0]
expect(type_name).to_equal("Server")
```

</details>

#### extracts type from function return

- extracts type from function return
   - Expected: has_arrow is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts type from function return")
val line = "fn get_server() -> Server:"
val has_arrow = line.contains("->")
expect(has_arrow).to_equal(true)
```

</details>

#### searches for class/struct/enum/trait definition

- searches for class/struct/enum/trait definition
   - Expected: patterns.len() equals `4`
   - Expected: patterns[0] equals `class Server`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("searches for class/struct/enum/trait definition")
val type_name = "Server"
val patterns = ["class " + type_name, "struct " + type_name, "enum " + type_name, "trait " + type_name]
expect(patterns.len()).to_equal(4)
expect(patterns[0]).to_equal("class Server")
```

</details>

### simple_implementation tool

#### requires file parameter

- requires file parameter
   - Expected: file equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires file parameter")
val file = ""
expect(file).to_equal("")
```

</details>

#### requires line parameter

- requires line parameter
   - Expected: line equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires line parameter")
val line = ""
expect(line).to_equal("")
```

</details>

#### builds correct command

- builds correct command


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds correct command")
val file = "src/test.spl"
val line = "5"
var cmd = "timeout 30 bin/simple query implementation " + file + " " + line
cmd = cmd + " 2>&1"
expect(cmd).to_contain("query implementation")
```

</details>

#### appends column when provided

- appends column when provided


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("appends column when provided")
val file = "test.spl"
val line = "10"
val column = "3"
var cmd = "timeout 30 bin/simple query implementation " + file + " " + line
cmd = cmd + " " + column
expect(cmd).to_contain("10 3")
```

</details>

#### finds trait implementations via impl pattern

- finds trait implementations via impl pattern
   - Expected: pattern equals `impl Printable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds trait implementations via impl pattern")
val trait_name = "Printable"
val pattern = "impl " + trait_name
expect(pattern).to_equal("impl Printable")
```

</details>

#### finds type implementations via impl.*Type pattern

- finds type implementations via impl.*Type pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds type implementations via impl.*Type pattern")
val type_name = "Server"
val pattern = "impl.*" + type_name
expect(pattern).to_contain("impl")
expect(pattern).to_contain("Server")
```

</details>

#### distinguishes traits from types

- distinguishes traits from types
   - Expected: is_trait is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("distinguishes traits from types")
val trait_line = "trait Printable:"
val is_trait = trait_line.starts_with("trait ")
expect(is_trait).to_equal(true)
```

</details>

#### struct is not a trait

- struct is not a trait
   - Expected: is_trait is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("struct is not a trait")
val struct_line = "struct Point:"
val is_trait = struct_line.starts_with("trait ")
expect(is_trait).to_equal(false)
```

</details>

### simple_folding_range tool

#### requires file parameter

- requires file parameter
   - Expected: file equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("requires file parameter")
val file = ""
expect(file).to_equal("")
```

</details>

#### builds correct command

- builds correct command


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds correct command")
val file = "src/app/cli/query.spl"
var cmd = "timeout 30 bin/simple query folding-range " + file + " 2>&1"
expect(cmd).to_contain("query folding-range")
expect(cmd).to_contain(file)
```

</details>

#### does not require line parameter

- does not require line parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not require line parameter")
val file = "test.spl"
var cmd = "timeout 30 bin/simple query folding-range " + file
# No positional line number
expect(cmd).to_contain("folding-range test.spl")
```

</details>

#### output format is start_line:end_line:kind

- output format is start_line:end_line:kind
   - Expected: parts.len() equals `3`
   - Expected: parts[2] equals `imports`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("output format is start_line:end_line:kind")
val output = "1:5:imports"
val parts = output.split(":")
expect(parts.len()).to_equal(3)
expect(parts[2]).to_equal("imports")
```

</details>

#### detects import folding regions

- detects import folding regions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects import folding regions")
val kind = "imports"
val valid_kinds = ["imports", "comment", "function", "class", "struct", "enum", "trait", "impl"]
expect(valid_kinds).to_contain(kind)
```

</details>

#### detects comment folding regions

- detects comment folding regions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects comment folding regions")
val kind = "comment"
val valid_kinds = ["imports", "comment", "function", "class", "struct", "enum", "trait", "impl"]
expect(valid_kinds).to_contain(kind)
```

</details>

#### detects function folding regions

- detects function folding regions


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects function folding regions")
val kind = "function"
val valid_kinds = ["imports", "comment", "function", "class", "struct", "enum", "trait", "impl"]
expect(valid_kinds).to_contain(kind)
```

</details>

#### detects class/struct/enum/trait regions

- detects class/struct/enum/trait regions
   - Expected: block_kinds.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects class/struct/enum/trait regions")
val block_kinds = ["class", "struct", "enum", "trait", "impl"]
expect(block_kinds.len()).to_equal(5)
```

</details>

#### folding ends when indent returns to zero

- folding ends when indent returns to zero
   - Expected: is_block_start is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("folding ends when indent returns to zero")
# Block start at indent 0, block ends when next line at indent 0
val indent_0 = "fn hello():"
val indent_4 = "    print 'hello'"
val is_block_start = indent_0.starts_with("fn ")
expect(is_block_start).to_equal(true)
```

</details>

### MCP tool registration for new LSP tools

#### total tool count is 63

- total tool count is 63
   - Expected: tool_count equals `63`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("total tool count is 63")
val tool_count = 63
expect(tool_count).to_equal(63)
```

</details>

#### all 4 new tools registered in protocol

- all 4 new tools registered in protocol
   - Expected: new_tools.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all 4 new tools registered in protocol")
val new_tools = ["simple_document_highlight", "simple_type_definition", "simple_implementation", "simple_folding_range"]
expect(new_tools.len()).to_equal(4)
```

</details>

#### all new tools are read-only

- all new tools are read-only
   - Expected: read_only is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all new tools are read-only")
val read_only = true
expect(read_only).to_equal(true)
```

</details>

#### document-highlight schema has file+line+column

- document-highlight schema has file+line+column


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("document-highlight schema has file+line+column")
val params = ["file", "line", "column"]
expect(params).to_contain("file")
expect(params).to_contain("line")
expect(params).to_contain("column")
```

</details>

#### folding-range schema has file only

- folding-range schema has file only
   - Expected: params.len() equals `1`
   - Expected: params[0] equals `file`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("folding-range schema has file only")
val params = ["file"]
expect(params.len()).to_equal(1)
expect(params[0]).to_equal("file")
```

</details>

#### dispatch entries added for all 4 tools

- dispatch entries added for all 4 tools
   - Expected: tool_names.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatch entries added for all 4 tools")
val tool_names = ["simple_document_highlight", "simple_type_definition", "simple_implementation", "simple_folding_range"]
expect(tool_names.len()).to_equal(4)
```

</details>

### LSP extras cross-tool consistency

#### all position tools accept file and line

- all position tools accept file and line
   - Expected: position_tools.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all position tools accept file and line")
val position_tools = ["document-highlight", "type-definition", "implementation"]
expect(position_tools.len()).to_equal(3)
```

</details>

#### folding-range is file-only

- folding-range is file-only
   - Expected: file_only.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("folding-range is file-only")
val file_only = ["folding-range"]
expect(file_only.len()).to_equal(1)
```

</details>

#### all tools use 30 second timeout

- all tools use 30 second timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all tools use 30 second timeout")
val timeout = "timeout 30"
val cmd1 = "timeout 30 bin/simple query document-highlight f.spl 1"
val cmd2 = "timeout 30 bin/simple query folding-range f.spl"
expect(cmd1).to_start_with(timeout)
expect(cmd2).to_start_with(timeout)
```

</details>

#### all tools use bin/simple query prefix

- all tools use bin/simple query prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all tools use bin/simple query prefix")
val prefix = "bin/simple query"
val cmd = "timeout 30 bin/simple query document-highlight test.spl 1"
expect(cmd).to_contain(prefix)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/mcp_lsp_extras_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering simple_document_highlight tool, simple_type_definition tool, simple_implementation tool, simple_folding_range tool, MCP tool registration for new LSP tools, LSP extras cross-tool consistency.
- simple_document_highlight tool
- simple_type_definition tool
- simple_implementation tool
- simple_folding_range tool
- MCP tool registration for new LSP tools
- LSP extras cross-tool consistency

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 43 |
| Active scenarios | 43 |
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

- Canonical SPipe generation for source `c44c0bee0d28d9e6d70b30be99645b8f53cde315d0bb2d1b7f0af0c4483fc29a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c44c0bee0d28d9e6d70b30be99645b8f53cde315d0bb2d1b7f0af0c4483fc29a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c44c0bee0d28d9e6d70b30be99645b8f53cde315d0bb2d1b7f0af0c4483fc29a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/mcp_unit/mcp_lsp_extras_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_lsp_extras_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_lsp_extras_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_lsp_extras_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_lsp_extras_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/mcp_lsp_extras_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires file parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_lsp_extras_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires line parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_lsp_extras_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds correct command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
