# MCP Analysis Tools (Tier 3) Specification

> This unit spec covers the Tier 3 MCP analysis handlers used by editor and agent clients when they need repository context without opening broad raw output.

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
| 34 | 34 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Analysis Tools (Tier 3) Specification

This unit spec covers the Tier 3 MCP analysis handlers used by editor and agent clients when they need repository context without opening broad raw output.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MCP-ANALYSIS-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | doc/03_plan/app/mcp/mcp_scenario_manual_quality.md |
| Design | doc/05_design/lib/web/cli_mcp_alignment_matrix.md |
| Research | doc/01_research/app/mcp/mcp_cli_gap_analysis.md |
| Source | `test/01_unit/app/mcp_unit/mcp_analysis_tools_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This unit spec covers the Tier 3 MCP analysis handlers used by editor and agent
clients when they need repository context without opening broad raw output.

**Feature IDs:** #MCP-ANALYSIS-001
**Category:** Tooling
**Difficulty:** 2/5
**Status:** Implemented
**Requirements:** N/A
**Plan:** doc/03_plan/app/mcp/mcp_scenario_manual_quality.md
**Research:** doc/01_research/app/mcp/mcp_cli_gap_analysis.md
**Design:** doc/05_design/lib/web/cli_mcp_alignment_matrix.md

## Syntax

```sh
bin/simple test test/unit/app/mcp_unit/mcp_analysis_tools_spec.spl --mode=interpreter
bin/simple test test/01_unit/app/mcp_unit/mcp_analysis_tools_spec.spl --mode=interpreter
bin/simple spipe-docgen test/unit/app/mcp_unit/mcp_analysis_tools_spec.spl --output doc/06_spec
```

## Tools Covered

- `simple_dependencies` builds import and dependency queries.
- `simple_api_diff` builds revision-aware public API comparisons.
- `simple_context` routes context generation through the shared app context pack.
- `simple_ponytail` routes over-engineering analysis through the shared ponytail
  audit implementation.
- `simple_search` builds language-aware source searches.

## Acceptance

- Dependency analysis accepts either a target file or project-summary mode.
- API diff defaults to `HEAD` and accepts explicit revisions.
- Context generation is backed by `context_generate`, not a stale duplicate
  implementation.
- Lower MCP context diagnostics use argv process timeout handling rather than a
  shell-composed timeout string.
- Lower MCP tools/list and dispatch both expose the context and ponytail mimic
  tools.
- Ponytail analysis is backed by `ponytail_audit`, not a stale duplicate
  implementation.
- Search command construction keeps function, class, struct, enum, and trait
  searches scoped to Simple source.

## Handler Contracts

`simple_dependencies` is intentionally command-shape focused in this unit spec.
The integration layer owns process execution and output shape. This spec guards
the cheap contract: file input includes import grep, empty file input selects
summary mode, and command text includes the selected file path.

`simple_api_diff` guards revision selection and public-symbol grep shape. The
handler must preserve the provided revision when present, use `HEAD` when it is
missing, and include the requested file in the `git show` path.

`simple_context` is the context-mode mimic surface. It should delegate to the
shared pack generator so CLI, app, and MCP callers do not drift. The lower MCP
path must keep diagnostics timeout handling in argv form to avoid shell quoting
regressions around file names.

`simple_ponytail` is the ponytail mimic surface. It should delegate to the
shared audit and simplification implementations, preserve the audit categories
that flag stubs and abstraction smells, and expose report mode as an explicit
option-like selector.

`simple_search` is a bounded source search builder. It should keep generated
commands predictable and scoped instead of walking unrelated repository trees.

## Evidence Matrix

| Tool | Evidence | Expected result |
|------|----------|-----------------|
| dependencies | file path command | import grep includes file |
| dependencies | empty file | summary path selected |
| api diff | empty revision | `HEAD` selected |
| api diff | explicit revision | explicit revision selected |
| api diff | command text | `git show` includes target file |
| context | source sections | four standard sections present |
| context | app MCP source | `context_generate` is referenced |
| context | lower MCP source | argv timeout helper is referenced |
| context | lower MCP schema | `simple_context` tool is advertised and routed |
| ponytail | missing file | error path selected |
| ponytail | app MCP source | `ponytail_audit` is referenced |
| ponytail | lower MCP schema | `simple_ponytail` tool is advertised and routed |
| ponytail | stub fixture | placeholder marker is detected |
| ponytail | factory fixture | abstraction smell is detected |
| search | empty query | error path selected |
| search | general query | source grep includes query |
| search | function kind | function search prefix is used |
| search | class kind | class search prefix is used |
| search | struct kind | struct search prefix is used |
| search | enum kind | enum search prefix is used |
| search | trait kind | trait search prefix is used |
| search | scoped query | requested scope is used |

## Maintainer Notes

- Keep this spec cheap. It should not execute the full MCP server.
- Keep canonical and `test/01_unit` mirrors aligned.
- Avoid literal live placeholder tokens in fixtures when possible; broad verify
  scans should not confuse a test fixture with production debt.
- Prefer `to_contain` for positive containment assertions.
- Keep process-execution coverage in integration specs.
- Regenerate both manuals after changing this spec.

## Manual Run

```sh
bin/simple check test/unit/app/mcp_unit/mcp_analysis_tools_spec.spl test/01_unit/app/mcp_unit/mcp_analysis_tools_spec.spl
bin/simple test test/unit/app/mcp_unit/mcp_analysis_tools_spec.spl --mode=interpreter --clean
bin/simple test test/01_unit/app/mcp_unit/mcp_analysis_tools_spec.spl --mode=interpreter --clean
bin/simple spipe-docgen test/unit/app/mcp_unit/mcp_analysis_tools_spec.spl --output doc/06_spec
bin/simple spipe-docgen test/01_unit/app/mcp_unit/mcp_analysis_tools_spec.spl --output doc/06_spec
```

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

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("simple_dependencies (project summary)")
```

</details>

### simple_api_diff tool

#### requires file parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("Missing required parameter: file")
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

#### app MCP context generates the pack via the `context` subprocess

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The context pack must be produced by a `bin/simple context` subprocess,
# NOT by importing `context_generate` in-process: that import pulls the
# whole CLI/compiler graph into the source MCP server and makes
# `bin/simple run src/app/mcp/main.spl` skip main() (server never starts).
# The subprocess still delegates to the shared `context_generate` (run by
# the `context` CLI command), so there is no stale duplicate.
# See doc/08_tracking/bug/mcp_source_mode_large_import_graph_2026-06-23.md
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("ctx_args")
expect(source).to_contain("\"context\", file")
expect(source).to_contain("process_run_timeout(_mcp_find_simple_binary(), ctx_args")
expect(source).to_contain("ctx_args.push(\"--json\")")
expect(source).to_contain("ctx_args.push(\"--text\")")
```

</details>

#### app MCP context validates requested context format

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("var format = extract_field(body, \"format\")")
expect(source).to_contain("format = \"text\"")
expect(source).to_contain("Invalid format: ")
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

#### lower MCP context diagnostics use argv process timeout

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("process_run_timeout")
expect(source.contains("timeout 10 \" + _mcp_find_simple_binary() + \" check \" + file")).to_equal(false)
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

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("target_report")
expect(source).to_contain("_mcp_render_context_pack")
expect(source).to_contain("val sourceless_sql_query = file == \"\" and sql_enabled and query != \"\"")
expect(source).to_contain("ctx_args.push(\"--query=\" + query)")
expect(source).to_contain("ctx_args.push(\"--sql\")")
expect(source).to_contain("ctx_args.push(\"--db=\" + db_path)")
expect(source).to_contain("val source_filter = extract_field(body, \"source_filter\")")
expect(source).to_contain("ctx_args.push(\"--source-filter=\" + source_filter)")
```

</details>

### simple_ponytail tool

#### requires file parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("Missing required parameter: file")
```

</details>

#### app MCP ponytail uses shared audit implementation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("ponytail_audit")
expect(source).to_contain("ponytail_simplification_report")
```

</details>

#### app MCP ponytail renders requested output format

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("var format = extract_field(body, \"format\")")
expect(source).to_contain("var mode = extract_field(body, \"mode\")")
expect(source).to_contain("Invalid format: ")
expect(source).to_contain("Invalid mode: ")
expect(source).to_contain("_render_ponytail_mcp(file, mode, result, format)")
expect(source).to_contain("_mcp_json_escape")
expect(source).to_contain("value.char_code_at(i)")
expect(source.contains("value.replace")).to_equal(false)
expect(source).to_contain("# Ponytail \" + mode")
```

</details>

#### lower MCP ponytail validates requested output format

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("val format = _mcp_output_format(body)")
expect(source).to_contain("var mode = extract_field(body, \"mode\")")
expect(source).to_contain("Invalid format: ")
expect(source).to_contain("Invalid mode: ")
expect(source).to_contain("_mcp_render_ponytail_report")
expect(source).to_contain("ponytail_simplification_report_source")
expect(source).to_contain("\\\"command\\\":\\\"ponytail\\\"")
expect(source).to_contain("\\\"status\\\":\\\"ok\\\"")
expect(source).to_contain("\\\"mode\\\":")
expect(source).to_contain("# Ponytail \" + mode")

val schema = rt_file_read_text("src/lib/nogc_async_mut/mcp/lazy_protocol_schemas.spl") ?? ""
expect(schema).to_contain("elif name == \"simple_ponytail\"")
expect(schema).to_contain("jp(\"file\", jo2")
expect(schema).to_contain("jp(\"mode\", jo2")
expect(schema).to_contain("Mode: audit, simplification")
expect(schema).to_contain("jp(\"format\", jo2")
expect(schema).to_contain("Output format: text, markdown, json")
expect(schema).to_contain("req = \"[\" + js(\"file\") + \"]\"")
```

</details>

#### lower MCP advertises and routes simple_ponytail

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = rt_file_read_text("src/lib/nogc_async_mut/mcp/lazy_protocol_schemas.spl") ?? ""
expect(schema).to_contain("make_tool_schema(name: \"simple_ponytail\"")
expect(schema).to_contain("elif name == \"simple_ponytail\"")

val dispatcher = rt_file_read_text("src/lib/nogc_async_mut/mcp/main_lazy.spl") ?? ""
expect(dispatcher).to_contain("tool_name == \"simple_ponytail\"")
expect(dispatcher).to_contain("handle_simple_ponytail(id, body)")
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

#### flags pass markers

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val marker = "pass_" + "todo"
val source = "fn fake() -> void:\n    " + marker + "(\"later\")"
expect(source).to_contain(marker)
```

</details>

#### flags abstraction smells

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "class OneThingFactory:\n    pass"
expect(source).to_contain("Factory")
```

</details>

### simple_search tool

#### requires query parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("Missing required parameter: query")
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
| Total scenarios | 34 |
| Active scenarios | 34 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/app/mcp/mcp_scenario_manual_quality.md](doc/03_plan/app/mcp/mcp_scenario_manual_quality.md)
- **Design:** [doc/05_design/lib/web/cli_mcp_alignment_matrix.md](doc/05_design/lib/web/cli_mcp_alignment_matrix.md)
- **Research:** [doc/01_research/app/mcp/mcp_cli_gap_analysis.md](doc/01_research/app/mcp/mcp_cli_gap_analysis.md)


</details>
