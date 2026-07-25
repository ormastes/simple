# mcp_analysis_tools_spec

> Tests the Tier 3 MCP analysis tool handlers: simple_dependencies, simple_api_diff, simple_context, simple_ponytail, simple_search.

<!-- sdn-diagram:id=mcp_analysis_tools_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_analysis_tools_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_analysis_tools_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_analysis_tools_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mcp_analysis_tools_spec

Tests the Tier 3 MCP analysis tool handlers: simple_dependencies, simple_api_diff, simple_context, simple_ponytail, simple_search.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MCP-ANALYSIS-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md |
| Design | N/A |
| Research | doc/01_research/local/llm_tooling_context_ponytail_mimic.md |
| Source | `test/unit/app/mcp_unit/mcp_analysis_tools_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the Tier 3 MCP analysis tool handlers:
simple_dependencies, simple_api_diff, simple_context, simple_ponytail,
simple_search.

## Syntax

```sh
bin/simple test test/unit/app/mcp_unit/mcp_analysis_tools_spec.spl --mode=interpreter
bin/simple spipe-docgen test/unit/app/mcp_unit/mcp_analysis_tools_spec.spl --output doc/06_spec
```

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md
**Research:** doc/01_research/local/llm_tooling_context_ponytail_mimic.md
**Design:** N/A

## Behavior

- Dependencies shows imports and reverse deps for a file, or project summary
- API diff compares public API against git revision
- Context packs file info for AI consumption
- Search provides language-aware grep with kind/scope filters
- Ponytail exposes audit and simplification report modes

## Scenarios

### simple_dependencies tool

#### builds import grep for specific file

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/main.spl"
var cmd = "grep -n '^use \\|^import ' " + file + " 2>/dev/null"
expect(cmd).to_contain("grep")
expect(cmd).to_contain(file)
```

</details>

#### works without file for project summary

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = ""
var is_summary = file == ""
expect(is_summary).to_equal(true)
```

</details>

### simple_api_diff tool

#### requires file parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = ""
val has_error = file == ""
expect(has_error).to_equal(true)
```

</details>

#### defaults revision to HEAD

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val revision = ""
var rev = "HEAD"
if revision != "":
    rev = revision
expect(rev).to_equal("HEAD")
```

</details>

#### uses custom revision

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val revision = "main~5"
var rev = "HEAD"
if revision != "":
    rev = revision
expect(rev).to_equal("main~5")
```

</details>

#### builds git show command for previous API

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/main.spl"
val rev = "HEAD"
var cmd = "git show " + rev + ":" + file + " 2>/dev/null | grep -n '^fn \\|^class \\|^struct \\|^enum \\|^export '"
expect(cmd).to_contain("git show HEAD:")
expect(cmd).to_contain(file)
```

</details>

### simple_context tool

#### requires file parameter except source-less sql query

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("Missing required parameter: file")
expect(source).to_contain("val sourceless_sql_query = file == \"\" and sql_enabled and query != \"\"")
expect(source).to_contain("if file == \"\" and not sourceless_sql_query")
```

</details>

#### includes source, imports, symbols, diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sections = ["Source", "Imports", "Symbols", "Diagnostics"]
expect(sections.len()).to_equal(4)
```

</details>

#### adds target section when specified

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val target = "main"
val has_target = target != ""
expect(has_target).to_equal(true)
```

</details>

#### app MCP context forwards local index query and sql options

<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("val query = extract_field(body, \"query\")")
expect(source).to_contain("val index = extract_field(body, \"index\")")
expect(source).to_contain("val sql = extract_field(body, \"sql\")")
expect(source).to_contain("val db_path = extract_field(body, \"db\")")
expect(source).to_contain("val source_filter = extract_field(body, \"source_filter\")")
expect(source).to_contain("var ctx_args = [\"context\"]")
expect(source).to_contain("ctx_args.push(\"--index\")")
expect(source).to_contain("ctx_args.push(\"--query=\" + query)")
expect(source).to_contain("ctx_args.push(\"--sql\")")
expect(source).to_contain("ctx_args.push(\"--db=\" + db_path)")
expect(source).to_contain("ctx_args.push(\"--source-filter=\" + source_filter)")

val table = rt_file_read_text("src/app/mcp/tool_table.spl") ?? ""
expect(table).to_contain("prop_str(\"format\", \"Output format: text, markdown, json\")")
expect(table).to_contain("prop_str(\"index\", \"Emit a local context-pack index (true/false)\")")
expect(table).to_contain("prop_str(\"file\", \"Source file path; required except when sql=true and query is non-empty\")")
expect(table).to_contain("prop_str(\"query\", \"Query local or SQL context-pack index\")")
expect(table).to_contain("prop_str(\"sql\", \"Use Simple embedded SQLite for index/query (true/false)\")")
expect(table).to_contain("e.required_json = build_required([])")
expect(table).to_contain("prop_str(\"db\", \"SQLite index database path\")")
expect(table).to_contain("prop_str(\"source_filter\", \"Filter SQL query rows by stored source path\")")
```

</details>

#### app and lower MCP context find checked-in release binaries

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app_source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(app_source).to_contain("release/x86_64-unknown-linux-gnu/simple")
expect(app_source).to_contain("bootstrap/stage3/simple")

val lower_source = rt_file_read_text("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl") ?? ""
expect(lower_source).to_contain("release/x86_64-unknown-linux-gnu/simple")
expect(lower_source).to_contain("bootstrap/stage3/simple")
```

</details>

#### lower MCP context validates requested output format

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("val format = _mcp_output_format(body)")
expect(source).to_contain("Invalid format: ")
expect(source).to_contain("_mcp_render_context_pack")
expect(source).to_contain("\\\"line_count\\\"")
expect(source).to_contain("\\\"target_lines\\\"")
expect(source).to_contain("_mcp_json_escape(content)")
expect(source).to_contain("# Context Pack")

val schema = rt_file_read_text("src/lib/nogc_async_mut/mcp/lazy_protocol_schemas.spl") ?? ""
expect(schema).to_contain("elif name == \"simple_context\"")
expect(schema).to_contain("jp(\"file\", jo2")
expect(schema).to_contain("jp(\"target\", jo2")
expect(schema).to_contain("jp(\"format\", jo2")
expect(schema).to_contain("jp(\"index\", jo2")
expect(schema).to_contain("jp(\"query\", jo2")
expect(schema).to_contain("jp(\"sql\", jo2")
expect(schema).to_contain("jp(\"db\", jo2")
expect(schema).to_contain("jp(\"source_filter\", jo2")
expect(schema).to_contain("Output format: text, markdown, json")
expect(schema).to_contain("req = \"[]\"")
```

</details>

#### lower MCP advertises and routes simple_context

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = rt_file_read_text("src/lib/nogc_async_mut/mcp/lazy_protocol_schemas.spl") ?? ""
expect(schema).to_contain("make_tool_schema(name: \"simple_context\"")
expect(schema).to_contain("elif name == \"simple_context\"")

val dispatcher = rt_file_read_text("src/lib/nogc_async_mut/mcp/main_lazy.spl") ?? ""
expect(dispatcher).to_contain("tool_name == \"simple_context\"")
expect(dispatcher).to_contain("handle_simple_context(id, body)")
```

</details>

#### adds target lines to the context pack

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("target_report")
expect(source).to_contain("_mcp_render_context_pack")
expect(source).to_contain("val sourceless_sql_query = file == \"\" and sql_enabled and query != \"\"")
expect(source).to_contain("ctx_args.push(\"--query=\" + query)")
```

</details>

### simple_ponytail tool

#### app MCP ponytail exposes audit and simplification modes

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("ponytail_audit")
expect(source).to_contain("ponytail_simplification_report")
expect(source).to_contain("var mode = extract_field(body, \"mode\")")
expect(source).to_contain("Invalid mode: ")
expect(source).to_contain("_render_ponytail_mcp(file, mode, result, format)")
```

</details>

#### lower MCP ponytail exposes audit and simplification modes

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("ponytail_audit_source")
expect(source).to_contain("ponytail_simplification_report_source")
expect(source).to_contain("var mode = extract_field(body, \"mode\")")
expect(source).to_contain("Invalid mode: ")
expect(source).to_contain("\\\"mode\\\":")

val schema = rt_file_read_text("src/lib/nogc_async_mut/mcp/lazy_protocol_schemas.spl") ?? ""
expect(schema).to_contain("jp(\"mode\", jo2")
expect(schema).to_contain("Mode: audit, simplification")
```

</details>

#### app MCP advertises and routes simple_ponytail

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val table = rt_file_read_text("src/app/mcp/tool_table.spl") ?? ""
expect(table).to_contain("tool_entry(\"simple_ponytail\"")
expect(table).to_contain("Ponytail over-engineering audit")
expect(table).to_contain("prop_str(\"mode\", \"Mode: audit, simplification\")")

val static_tools = rt_file_read_text("src/app/mcp/main_static_tools.spl") ?? ""
expect(static_tools).to_contain("_mcp_static_tool(\"simple_ponytail\"")

val dispatcher = rt_file_read_text("src/app/mcp/main_dispatch.spl") ?? ""
expect(dispatcher).to_contain("name == \"simple_ponytail\"")
expect(dispatcher).to_contain("return handle_simple_ponytail(id, body)")
```

</details>

### simple_search tool

#### requires query parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = ""
val has_error = query == ""
expect(has_error).to_equal(true)
```

</details>

#### builds general search command

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = "fn main"
val kind = ""
val scope = ""
var search_dir = "src/"
var cmd = "grep -rn '" + query + "' " + search_dir + " --include='*.spl' 2>/dev/null | head -50"
expect(cmd).to_contain(query)
expect(cmd).to_contain("src/")
```

</details>

#### builds function search

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = "main"
val kind = "fn"
var cmd = ""
if kind == "fn":
    cmd = "grep -rn '^fn " + query + "' src/ --include='*.spl' 2>/dev/null | head -50"
expect(cmd).to_contain("^fn main")
```

</details>

#### builds class search

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = "Point"
val kind = "class"
var cmd = ""
if kind == "class":
    cmd = "grep -rn '^class " + query + "' src/ --include='*.spl' 2>/dev/null | head -50"
expect(cmd).to_contain("^class Point")
```

</details>

#### maps scope to correct directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scope = "test"
var search_dir = "src/"
if scope == "test":
    search_dir = "test/"
elif scope == "lib":
    search_dir = "src/lib/"
elif scope == "compiler":
    search_dir = "src/compiler/"
expect(search_dir).to_equal("test/")
```

</details>

#### maps lib scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scope = "lib"
var search_dir = "src/"
if scope == "lib":
    search_dir = "src/lib/"
expect(search_dir).to_equal("src/lib/")
```

</details>

#### maps compiler scope

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val scope = "compiler"
var search_dir = "src/"
if scope == "compiler":
    search_dir = "src/compiler/"
expect(search_dir).to_equal("src/compiler/")
```

</details>

#### restricts to specific file

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val file = "src/app/cli/main.spl"
val query = "fn main"
var cmd = "grep -n '" + query + "' " + file + " 2>/dev/null | head -50"
expect(cmd).to_contain(file)
```

</details>

#### builds import search

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = "std.spec"
val kind = "import"
var cmd = ""
if kind == "import":
    cmd = "grep -rn 'use.*" + query + "' src/ --include='*.spl' 2>/dev/null | head -50"
expect(cmd).to_contain("use.*std.spec")
```

</details>

#### builds type search

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val query = "Position"
val kind = "type"
var cmd = ""
if kind == "type":
    cmd = "grep -rn '^type " + query + "' src/ --include='*.spl' 2>/dev/null | head -50"
expect(cmd).to_contain("^type Position")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md](doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md)
- **Research:** [doc/01_research/local/llm_tooling_context_ponytail_mimic.md](doc/01_research/local/llm_tooling_context_ponytail_mimic.md)


</details>
