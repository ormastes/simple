# Context/Ponytail Mimic System Specification

> This system spec verifies the shipped tool surfaces for the local context-mode mimic and Ponytail mimic pair. It proves the CLI, app MCP, lower MCP, operator guide, and verification guard all describe the same public contract.

<!-- sdn-diagram:id=context_ponytail_mimic_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=context_ponytail_mimic_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

context_ponytail_mimic_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=context_ponytail_mimic_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Context/Ponytail Mimic System Specification

This system spec verifies the shipped tool surfaces for the local context-mode mimic and Ponytail mimic pair. It proves the CLI, app MCP, lower MCP, operator guide, and verification guard all describe the same public contract.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md |
| Plan | doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md |
| Design | doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md |
| Research | doc/01_research/local/llm_tooling_context_ponytail_mimic.md |
| Source | `test/03_system/app/tooling/feature/context_ponytail_mimic_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This system spec verifies the shipped tool surfaces for the local
context-mode mimic and Ponytail mimic pair. It proves the CLI, app MCP, lower
MCP, operator guide, and verification guard all describe the same public
contract.

## Syntax

The SQL-backed context mimic supports:

- `context <file> --sql --index --db=<path>`
- `context --sql --query=<text> --db=<path> --source-filter=<path>`
- MCP `simple_context` with `sql=true`, `query`, `db`, and optional `source_filter`
- MCP `simple_ponytail` with `mode` set to `audit` or `simplification`

## Examples

Index two source files into a persisted context database, then query the
database without a source argument while filtering to one stored source path.
The filtered query must include the selected source content and exclude content
from the other indexed source.

## Operator Contract

The context mimic is intentionally CLI-backed. App MCP and lower MCP build the
same argument vector that an operator would run locally, so source-mode servers
do not import the full context/compiler graph into request handlers. The
observable contract is therefore the subprocess input and public response text:
`--sql`, `--query`, `--db`, and `--source-filter` must survive all routing
layers.

The source-less SQL query shape is deliberately narrow. A missing `file` is
accepted only when `sql=true` and `query` is non-empty. Local context generation,
local index, source-backed SQL index, and source-backed SQL query still require
a source file. This keeps accidental empty-file requests from becoming hidden
database queries.

`source_filter` narrows rows after the persisted context database is queried.
The filter matches the stored source path exactly or as a path suffix so callers
can pass either the full fixture path or a basename-style path. A filtered query
must report one selected source without leaking content from another indexed
source with the same marker.

The Ponytail mimic exposes two modes through the same tool registry:

- `audit` returns over-engineering findings.
- `simplification` returns cut/replace guidance.

Both app MCP and lower MCP must advertise these modes in schema metadata and
dispatch to shared handler logic.

## Coverage Matrix

| Requirement | Evidence |
|-------------|----------|
| REQ-012 | CLI accepts source-less persisted SQL query with `--query` and `--db`. |
| REQ-013 | App MCP advertises and forwards `simple_context` SQL query fields. |
| REQ-014 | SQL `source_filter` is documented and excludes non-matching rows. |
| REQ-015 | Lower MCP mirrors app MCP schema and handler routing. |

## Failure Modes

- Missing ordinary source file remains an error path.
- Empty SQL query returns explicit `empty_query` output.
- Missing or unavailable SQL database returns explicit `unavailable` output.
- No SQL matches returns explicit `no_matches` output.
- Public output must render absence as text such as `none`, `empty_query`,
  `no_matches`, or `unavailable`.
- Public output must not expose the internal absence marker.

## Verification Notes

This spec executes the real `src/app/context/main.spl` CLI through the current
Simple runtime for the persisted SQL slice. Source-level MCP checks are limited
to schema and argument-forwarding contracts so the test remains deterministic
without starting a live MCP server. The public absence-rendering shell guard is
also checked by source reference to keep release verification tied to this
manual and the context/ponytail generated specs.

## Out of Scope

- A general SQL planner or arbitrary SQL grammar.
- Importing the context compiler graph directly into MCP request handlers.
- Replacing Ponytail logic with a separate dashboard-only implementation.
- Treating fixture-only output as live vLLM, fine-tune, or Torch evidence.

## Evidence Ownership

The merge owner for this slice is the LLM tooling lane. Final review must check
the executable spec, generated manual, MCP guide, and absence-rendering guard
together so future schema or CLI changes do not drift across surfaces.

## Scenarios

### context/ponytail mimic system surface

#### REQ-012 exposes source-less SQL context DB query through the CLI

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cli = read("src/app/context/main.spl")
expect(cli).to_contain("context_args_allow_sourceless_sql_query(args)")
expect(cli).to_contain("context_sql_query_packs_by_source([], \"\", sourceless_query, sourceless_source_filter, sourceless_db_path, sourceless_format)")
expect(cli).to_contain("--source-filter=")
```

</details>

#### REQ-012 and REQ-014 execute persisted source-less SQL CLI queries

- dir create all
- file write
- file write
   - Expected: index_code equals `0`
   - Expected: query_code equals `0`
   - Expected: query_output.split("beta_excluded").len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dir_create_all("build/test/context_ponytail_system")
val source_path = "build/test/context_ponytail_system/alpha.spl"
val beta_source_path = "build/test/context_ponytail_system/beta.spl"
val db_path = "build/test/context_ponytail_system/context_cli.db"
file_write(source_path, "fn alpha_context() -> text:\n    \"shared_context_marker alpha_only\"\n")
file_write(beta_source_path, "fn beta_context() -> text:\n    \"shared_context_marker beta_excluded\"\n")

val (index_output, index_code) = _run_context_cli([source_path, beta_source_path, "--sql", "--index", "--db=" + db_path, "--text", "--no-progress"])
expect(index_code).to_equal(0)
expect(index_output).to_contain("status: ready")
expect(index_output).to_contain("pack_count: 2")

val (query_output, query_code) = _run_context_cli(["--sql", "--query=shared_context_marker", "--db=" + db_path, "--source-filter=" + source_path, "--text", "--no-progress"])
expect(query_code).to_equal(0)
expect(query_output).to_contain("status: ready")
expect(query_output).to_contain("source_filter: " + source_path)
expect(query_output).to_contain("matches: 1")
expect(query_output).to_contain("alpha_only")
expect(query_output.split("beta_excluded").len()).to_equal(1)
```

</details>

#### REQ-013 and REQ-015 expose SQL query and source filter through app MCP

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = read("src/app/mcp/main_lazy_query_tools.spl")
val table = read("src/app/mcp/tool_table.spl")
val static_tools = read("src/app/mcp/main_static_tools.spl")
val dispatch = read("src/app/mcp/main_dispatch.spl")
expect(handler).to_contain("val sourceless_sql_query = file == \"\" and sql_enabled and query != \"\"")
expect(handler).to_contain("if file == \"\" and not sourceless_sql_query")
expect(handler).to_contain("ctx_args.push(\"--query=\" + query)")
expect(handler).to_contain("ctx_args.push(\"--sql\")")
expect(handler).to_contain("ctx_args.push(\"--db=\" + db_path)")
expect(handler).to_contain("ctx_args.push(\"--source-filter=\" + source_filter)")
expect(table).to_contain("tool_entry(\"simple_context\"")
expect(table).to_contain("prop_str(\"source_filter\", \"Filter SQL query rows by stored source path\")")
expect(table).to_contain("e.required_json = build_required([])")
expect(static_tools).to_contain("_mcp_static_tool(\"simple_context\"")
expect(dispatch).to_contain("return handle_simple_context(id, body)")
```

</details>

#### REQ-013 and REQ-015 expose SQL query and source filter through lower MCP

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = read("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl")
val schema = read("src/lib/nogc_async_mut/mcp/lazy_protocol_schemas.spl")
val dispatch = read("src/lib/nogc_async_mut/mcp/main_lazy.spl")
expect(handler).to_contain("val sourceless_sql_query = file == \"\" and sql_enabled and query != \"\"")
expect(handler).to_contain("if file == \"\" and not sourceless_sql_query")
expect(handler).to_contain("ctx_args.push(\"--sql\")")
expect(handler).to_contain("ctx_args.push(\"--db=\" + db_path)")
expect(handler).to_contain("ctx_args.push(\"--source-filter=\" + source_filter)")
expect(schema).to_contain("make_tool_schema(name: \"simple_context\"")
expect(schema).to_contain("jp(\"source_filter\", jo2")
expect(schema).to_contain("req = \"[]\"")
expect(dispatch).to_contain("tool_name == \"simple_context\"")
expect(dispatch).to_contain("handle_simple_context(id, body)")
```

</details>

#### REQ-014 preserves SQL source filter documentation and absence-safe public output

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context_ops = read("src/app/io/context_ops.spl")
val guide = read("doc/07_guide/app/mcp/mcp.md")
val guard = read("scripts/check/check-llm-tooling-public-absence-rendering.shs")
expect(context_ops).to_contain("context_sql_query_packs_by_source")
expect(context_ops).to_contain("source_filter")
expect(guide).to_contain("context --sql --query=<text> --db=<path> --source-filter=<text>")
expect(guide).to_contain("The MCP tool accepts `file`, optional `target`, `format`")
expect(guide).to_contain("source_filter")
expect(guard).to_contain("llm_tooling_context_ponytail_mimic.md")
expect(guard).to_contain("context_generate_spec.md")
expect(guard).to_contain("ponytail_audit_spec.md")
expect(guard).to_contain("Public absence-rendering gate")
```

</details>

#### exposes Ponytail audit and simplification modes through app and lower MCP

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app_handler = read("src/app/mcp/main_lazy_query_tools.spl")
val app_table = read("src/app/mcp/tool_table.spl")
val lower_handler = read("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl")
val lower_schema = read("src/lib/nogc_async_mut/mcp/lazy_protocol_schemas.spl")
expect(app_handler).to_contain("ponytail_audit")
expect(app_handler).to_contain("ponytail_simplification_report")
expect(app_handler).to_contain("Invalid mode: ")
expect(app_handler).to_contain("_render_ponytail_mcp(file, mode, result, format)")
expect(app_table).to_contain("prop_str(\"mode\", \"Mode: audit, simplification\")")
expect(lower_handler).to_contain("ponytail_audit_source")
expect(lower_handler).to_contain("ponytail_simplification_report_source")
expect(lower_handler).to_contain("_mcp_render_ponytail_report")
expect(lower_schema).to_contain("make_tool_schema(name: \"simple_ponytail\"")
expect(lower_schema).to_contain("Mode: audit, simplification")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md](doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md)
- **Plan:** [doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md](doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md)
- **Design:** [doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md](doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md)
- **Research:** [doc/01_research/local/llm_tooling_context_ponytail_mimic.md](doc/01_research/local/llm_tooling_context_ponytail_mimic.md)


</details>
