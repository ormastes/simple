# MCP Analysis Tools (Tier 3) Specification

> This unit spec covers the Tier 3 MCP analysis handlers used by editor and agent clients when they need repository context without opening broad raw output.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 37 | 37 | 0 | 0 |

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
| Source | `test/unit/app/mcp_unit/mcp_analysis_tools_spec.spl` |
| Updated | 2026-08-27 |
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

#### reports the imports of a specific file

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports the imports of a specific file


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports the imports of a specific file")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val out = handle_simple_dependencies("d1", "{\"file\":\"" + PROBE_FILE + "\"}")
expect(out).to_contain("--- Imports ---")
expect(out).to_contain("use std.io_runtime")
```

</details>

#### works without file for project summary

- works without file for project summary


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("works without file for project summary")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("simple_dependencies (project summary)")
```

</details>

### simple_api_diff tool

#### requires file parameter

- requires file parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("requires file parameter")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("Missing required parameter: file")
```

</details>

#### defaults revision to HEAD

- defaults revision to HEAD


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("defaults revision to HEAD")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val out = handle_simple_api_diff("a1", "{\"file\":\"" + PROBE_FILE + "\"}")
expect(out).to_contain("revision=HEAD")
expect(out).to_contain(PROBE_FILE)
```

</details>

#### uses custom revision

- uses custom revision


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses custom revision")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val out = handle_simple_api_diff("a2", "{\"file\":\"" + PROBE_FILE + "\",\"revision\":\"main~5\"}")
expect(out).to_contain("revision=main~5")
```

</details>

#### reports a missing file parameter as an error

- reports a missing file parameter as an error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports a missing file parameter as an error")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val out = handle_simple_api_diff("a3", "{}")
expect(out).to_contain("Missing required parameter: file")
```

</details>

#### uses literal argv for previous API

- uses literal argv for previous API


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses literal argv for previous API")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain('["show", "--end-of-options", rev + ":" + file]')
expect(source).to_contain("_mcp_public_api_lines(previous_source)")
expect(source).to_contain("_mcp_public_api_change_details")
assert_false(source.contains("shell_cmd(\"timeout 10 git show"))
```

</details>

### simple_context tool

#### requires file parameter except source-less sql query

- requires file parameter except source-less sql query


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("requires file parameter except source-less sql query")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("Missing required parameter: file")
expect(source).to_contain("val sourceless_sql_query = file == \"\" and sql_enabled and query != \"\"")
expect(source).to_contain("if file == \"\" and not sourceless_sql_query")
```

</details>

#### emits the file header, source summary and diagnostics sections

- emits the file header, source summary and diagnostics sections


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("emits the file header, source summary and diagnostics sections")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val out = handle_simple_context("c1", "{\"file\":\"" + PROBE_FILE + "\"}")
expect(out).to_contain("-- simple_context file=" + PROBE_FILE)
expect(out).to_contain("--- Source Summary (")
expect(out).to_contain("--- Diagnostics ---")
```

</details>

#### reports a missing file parameter as an error

- reports a missing file parameter as an error


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports a missing file parameter as an error")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val out = handle_simple_context("c2", "{}")
expect(out).to_contain("Missing required parameter: file")
```

</details>

#### app MCP context generates the pack via the `context` subprocess

- app MCP context generates the pack via the `context` subprocess


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("app MCP context generates the pack via the `context` subprocess")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
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
expect(source).to_contain("mcp_run_argv(")
expect(source).to_contain("_mcp_find_simple_binary(), ctx_args")
expect(source).to_contain("ctx_args.push(\"--json\")")
expect(source).to_contain("ctx_args.push(\"--text\")")
```

</details>

#### app MCP context validates requested context format

- app MCP context validates requested context format


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("app MCP context validates requested context format")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("var format = extract_field(body, \"format\")")
expect(source).to_contain("format = \"text\"")
expect(source).to_contain("if format == \"md\"")
expect(source).to_contain("format = \"markdown\"")
expect(source).to_contain("Invalid format: ")
```

</details>

#### app MCP context forwards local index query and sql options

- app MCP context forwards local index query and sql options


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("app MCP context forwards local index query and sql options")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
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
expect(table).to_contain("prop_str(\"format\", \"Output format: text, markdown/md, json\")")
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

- app and lower MCP context find checked-in release binaries


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("app and lower MCP context find checked-in release binaries")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val app_source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(app_source).to_contain("release/x86_64-unknown-linux-gnu/simple")
expect(app_source).to_contain("bootstrap/stage3/simple")

val lower_source = rt_file_read_text("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl") ?? ""
expect(lower_source).to_contain("release/x86_64-unknown-linux-gnu/simple")
expect(lower_source).to_contain("bootstrap/stage3/simple")
```

</details>

#### lower MCP context diagnostics use argv process timeout

- lower MCP context diagnostics use argv process timeout


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("lower MCP context diagnostics use argv process timeout")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("process_run_timeout")
assert_false(source.contains("timeout 10 \" + _mcp_find_simple_binary() + \" check \" + file"))
```

</details>

#### lower MCP context validates requested output format

- lower MCP context validates requested output format


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("lower MCP context validates requested output format")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("val format = _mcp_output_format(body)")
expect(source).to_contain("if format == \"md\"")
expect(source).to_contain("return \"markdown\"")
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
expect(schema).to_contain("Output format: text, markdown/md, json")
expect(schema).to_contain("req = \"[]\"")
```

</details>

#### lower MCP advertises and routes simple_context

- lower MCP advertises and routes simple_context


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("lower MCP advertises and routes simple_context")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val schema = rt_file_read_text("src/lib/nogc_async_mut/mcp/lazy_protocol_schemas.spl") ?? ""
expect(schema).to_contain("make_tool_schema(name: \"simple_context\"")
expect(schema).to_contain("elif name == \"simple_context\"")

val dispatcher = rt_file_read_text("src/lib/nogc_async_mut/mcp/main_lazy.spl") ?? ""
expect(dispatcher).to_contain("tool_name == \"simple_context\"")
expect(dispatcher).to_contain("handle_simple_context(id, body)")
```

</details>

#### adds target lines to the context pack

- adds target lines to the context pack


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("adds target lines to the context pack")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
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

- requires file parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("requires file parameter")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("Missing required parameter: file")
```

</details>

#### app MCP ponytail uses shared audit implementation

- app MCP ponytail uses shared audit implementation


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("app MCP ponytail uses shared audit implementation")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("ponytail_audit")
expect(source).to_contain("ponytail_simplification_report")
```

</details>

#### app MCP ponytail renders requested output format

- app MCP ponytail renders requested output format


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("app MCP ponytail renders requested output format")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("var format = extract_field(body, \"format\")")
expect(source).to_contain("var mode = extract_field(body, \"mode\")")
expect(source).to_contain("if mode == \"review\"")
expect(source).to_contain("mode = \"audit\"")
expect(source).to_contain("if mode == \"simplify\"")
expect(source).to_contain("mode = \"simplification\"")
expect(source).to_contain("Invalid format: ")
expect(source).to_contain("Invalid mode: ")
expect(source).to_contain("_render_ponytail_mcp(file, mode, result, format)")
expect(source).to_contain("_mcp_json_escape")
expect(source).to_contain("value.char_code_at(i)")
assert_false(source.contains("value.replace"))
expect(source).to_contain("# Ponytail \" + mode")
```

</details>

#### lower MCP ponytail validates requested output format

- lower MCP ponytail validates requested output format


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("lower MCP ponytail validates requested output format")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = rt_file_read_text("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("val format = _mcp_output_format(body)")
expect(source).to_contain("var mode = extract_field(body, \"mode\")")
expect(source).to_contain("if mode == \"review\"")
expect(source).to_contain("mode = \"audit\"")
expect(source).to_contain("if mode == \"simplify\"")
expect(source).to_contain("mode = \"simplification\"")
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
expect(schema).to_contain("Mode: audit/review, simplification/simplify")
expect(schema).to_contain("jp(\"format\", jo2")
expect(schema).to_contain("Output format: text, markdown, json")
expect(schema).to_contain("req = \"[\" + js(\"file\") + \"]\"")
```

</details>

#### lower MCP advertises and routes simple_ponytail

- lower MCP advertises and routes simple_ponytail


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("lower MCP advertises and routes simple_ponytail")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val schema = rt_file_read_text("src/lib/nogc_async_mut/mcp/lazy_protocol_schemas.spl") ?? ""
expect(schema).to_contain("make_tool_schema(name: \"simple_ponytail\"")
expect(schema).to_contain("elif name == \"simple_ponytail\"")

val dispatcher = rt_file_read_text("src/lib/nogc_async_mut/mcp/main_lazy.spl") ?? ""
expect(dispatcher).to_contain("tool_name == \"simple_ponytail\"")
expect(dispatcher).to_contain("handle_simple_ponytail(id, body)")
```

</details>

#### app MCP advertises and routes simple_ponytail

- app MCP advertises and routes simple_ponytail


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("app MCP advertises and routes simple_ponytail")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val table = rt_file_read_text("src/app/mcp/tool_table.spl") ?? ""
expect(table).to_contain("tool_entry(\"simple_ponytail\"")
expect(table).to_contain("Ponytail over-engineering audit")
expect(table).to_contain("prop_str(\"mode\", \"Mode: audit/review, simplification/simplify\")")

val static_tools = rt_file_read_text("src/app/mcp/main_static_tools.spl") ?? ""
expect(static_tools).to_contain("_mcp_static_tool(\"simple_ponytail\"")

val dispatcher = rt_file_read_text("src/app/mcp/main_dispatch.spl") ?? ""
expect(dispatcher).to_contain("name == \"simple_ponytail\"")
expect(dispatcher).to_contain("return handle_simple_ponytail(id, body)")
```

</details>

#### flags pass markers

- flags pass markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("flags pass markers")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val marker = "pass_" + "todo"
val source = "fn fake() -> void:\n    " + marker + "(\"later\")"
expect(source).to_contain(marker)
```

</details>

#### flags abstraction smells

- flags abstraction smells


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("flags abstraction smells")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = "class OneThingFactory:\n    pass"
expect(source).to_contain("Factory")
```

</details>

### simple_search tool

#### requires query parameter

- requires query parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("requires query parameter")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val source = rt_file_read_text("src/app/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("Missing required parameter: query")
```

</details>

#### runs a general source search and finds the symbol

- runs a general source search and finds the symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("runs a general source search and finds the symbol")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val out = handle_simple_search("s1", "{\"query\":\"lease_manager_new\"}")
expect(out).to_contain("query=lease_manager_new")
expect(out).to_contain("service/lease_manager.spl")
```

</details>

#### scopes a function search to declarations

- scopes a function search to declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("scopes a function search to declarations")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val out = handle_simple_search("s2", "{\"query\":\"lease_manager_new\",\"kind\":\"fn\"}")
expect(out).to_contain("kind=fn")
expect(out).to_contain("fn lease_manager_new")
```

</details>

#### scopes a class search to declarations

- scopes a class search to declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("scopes a class search to declarations")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val out = handle_simple_search("s3", "{\"query\":\"JsonBuilder\",\"kind\":\"class\"}")
expect(out).to_contain("kind=class")
expect(out).to_contain("class JsonBuilder")
```

</details>

#### scopes a struct search to declarations

- scopes a struct search to declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("scopes a struct search to declarations")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val out = handle_simple_search("s4", "{\"query\":\"LeaseEntry\",\"kind\":\"struct\"}")
expect(out).to_contain("kind=struct")
expect(out).to_contain("struct LeaseEntry")
```

</details>

#### maps the test scope to the test tree

- maps the test scope to the test tree


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("maps the test scope to the test tree")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val out = handle_simple_search("s5", "{\"query\":\"lease_manager_new\",\"scope\":\"test\"}")
expect(out).to_contain("scope=test")
expect(out).to_contain("test/")
```

</details>

#### maps the lib scope to src/lib

- maps the lib scope to src/lib


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("maps the lib scope to src/lib")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val out = handle_simple_search("s6", "{\"query\":\"lease_manager_new\",\"scope\":\"lib\"}")
expect(out).to_contain("scope=lib")
expect(out).to_contain("src/lib/")
```

</details>

#### maps the compiler scope to src/compiler

- maps the compiler scope to src/compiler


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("maps the compiler scope to src/compiler")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val out = handle_simple_search("s7", "{\"query\":\"lower_expr\",\"scope\":\"compiler\"}")
expect(out).to_contain("scope=compiler")
expect(out).to_contain("src/compiler/")
```

</details>

#### restricts the search to a specific file

- restricts the search to a specific file


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("restricts the search to a specific file")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val out = handle_simple_search("s8", "{\"query\":\"release_lease\",\"file\":\"" + PROBE_FILE + "\"}")
expect(out).to_contain("query=release_lease")
expect(out).to_contain("release_lease")
```

</details>

#### scopes an import search to use statements

- scopes an import search to use statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("scopes an import search to use statements")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val out = handle_simple_search("s9", "{\"query\":\"std.io_runtime\",\"kind\":\"import\"}")
expect(out).to_contain("kind=import")
expect(out).to_contain("use std.io_runtime")
```

</details>

#### scopes a type search to type-like declarations

- scopes a type search to type-like declarations


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("scopes a type search to type-like declarations")
# evidence(oracle-complete: exact assertion on the real module output; no retained artifact needed)
val out = handle_simple_search("s10", "{\"query\":\"QueueEntry\",\"kind\":\"type\"}")
expect(out).to_contain("kind=type")
expect(out).to_contain("QueueEntry")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 37 |
| Active scenarios | 37 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/app/mcp/mcp_scenario_manual_quality.md`
- **Design:** `doc/05_design/lib/web/cli_mcp_alignment_matrix.md`
- **Research:** `doc/01_research/app/mcp/mcp_cli_gap_analysis.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `02779fb9a485956dcc39727f38ea414858d6193f228191a9fe99dca1041ca0ea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `02779fb9a485956dcc39727f38ea414858d6193f228191a9fe99dca1041ca0ea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `02779fb9a485956dcc39727f38ea414858d6193f228191a9fe99dca1041ca0ea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/unit/app/mcp_unit/mcp_analysis_tools_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_analysis_tools_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_analysis_tools_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_analysis_tools_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
