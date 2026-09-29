# MCP Context/Ponytail Dispatch Execution Specification

> This specification proves the Simple-owned context/Ponytail replacement tools execute through both MCP dispatch layers. App MCP coverage proves `simple_context` and `simple_ponytail` are not only registered in tool tables. Lower MCP coverage proves the shared lazy handlers execute the same replacement behavior instead of relying only on schema/source-shape checks.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Context/Ponytail Dispatch Execution Specification

This specification proves the Simple-owned context/Ponytail replacement tools execute through both MCP dispatch layers. App MCP coverage proves `simple_context` and `simple_ponytail` are not only registered in tool tables. Lower MCP coverage proves the shared lazy handlers execute the same replacement behavior instead of relying only on schema/source-shape checks.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md |
| Plan | doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md |
| Design | doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md |
| Research | doc/01_research/local/llm_tooling_context_ponytail_mimic.md |
| Source | `test/02_integration/app/mcp_context_ponytail_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This specification proves the Simple-owned context/Ponytail replacement tools
execute through both MCP dispatch layers. App MCP coverage proves
`simple_context` and `simple_ponytail` are not only registered in tool tables.
Lower MCP coverage proves the shared lazy handlers execute the same replacement
behavior instead of relying only on schema/source-shape checks.

## Examples

- `simple_context` renders a bounded context pack for a source file.
- `simple_context` can run a source-less embedded SQL query against a generated
  context DB.
- `simple_ponytail` renders an audit report from app and lower MCP handlers.

**Requirements:** doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md
**Plan:** doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md
**Design:** doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md
**Research:** doc/01_research/local/llm_tooling_context_ponytail_mimic.md

## Scenarios

### MCP context and Ponytail replacement dispatch

#### simple_context

#### executes through the app MCP dispatcher and returns a context pack

- executes through the app MCP dispatcher and returns a context pack


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("executes through the app MCP dispatcher and returns a context pack")
val args = """{"file":"src/app/mcp/main_dispatch.spl","target":"dispatch_tool","format":"text"}"""
val response = dispatch_tool_content("simple_context", args)
expect(response).to_contain("-- simple_context file=src/app/mcp/main_dispatch.spl --")
expect(response).to_contain("--- Context Pack ---")
expect(response).to_contain("dispatch_tool")
```

</details>

#### executes source-less embedded SQL query through the app MCP dispatcher

- executes source-less embedded SQL query through the app MCP dispatcher
   - Expected: response.split("sql_dispatch_broad").len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("executes source-less embedded SQL query through the app MCP dispatcher")
dir_create_all("build/test/mcp_context_ponytail_dispatch")
val source_path = "build/test/mcp_context_ponytail_dispatch/sql_dispatch_literal.spl"
val broad_path = "build/test/mcp_context_ponytail_dispatch/sql_dispatch_broad.spl"
val db_path = "build/test/mcp_context_ponytail_dispatch/context_dispatch.db"
file_write(source_path, "fn dispatch_sql_context_marker() -> text:\n    \"dispatch_sql_context_marker dispatch_sql_100%_exact sql_dispatch_only\"\n")
file_write(broad_path, "fn dispatch_sql_context_marker_broad() -> text:\n    \"dispatch_sql_context_marker dispatch_sql_100xxexact sql_dispatch_broad\"\n")

val index_output = context_sql_index_packs([source_path, broad_path], "ctx", db_path, "text")
expect(index_output).to_contain("status: ready")

val args = "{\"sql\":\"true\",\"query\":\"dispatch_sql_100%_exact\",\"db\":\"" + db_path + "\",\"format\":\"text\"}"
val response = dispatch_tool_content("simple_context", args)
expect(response).to_contain("-- simple_context sql query db=" + db_path + " --")
expect(response).to_contain("status: ready")
expect(response).to_contain("matches: 1")
expect(response).to_contain("sql_dispatch_only")
expect(response.split("sql_dispatch_broad").len()).to_equal(1)
```

</details>

#### renders MCP context and Ponytail absence without internal markers

- renders MCP context and Ponytail absence without internal markers


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("renders MCP context and Ponytail absence without internal markers")
dir_create_all("build/test/mcp_context_ponytail_dispatch")
val clean_path = "build/test/mcp_context_ponytail_dispatch/absence_clean.spl"
file_write(clean_path, "fn clean_marker() -> text:\n    \"absence_safe_context_marker\"\n")

val context_args = "{\"file\":\"" + clean_path + "\",\"target\":\"clean_marker\",\"format\":\"text\"}"
val app_context = dispatch_tool_content("simple_context", context_args)
val lower_context = lower_handle_simple_context("lower-absence-context", context_args)
expect(app_context).to_contain("status: ready")
expect(lower_context).to_contain("status: ready")
_expect_absence_marker_hidden(app_context)
_expect_absence_marker_hidden(lower_context)

val missing_context_args = """{"file":"build/test/mcp_context_ponytail_dispatch/missing_context.spl","format":"text"}"""
_expect_absence_marker_hidden(dispatch_tool_content("simple_context", missing_context_args))
_expect_absence_marker_hidden(lower_handle_simple_context("lower-missing-context", missing_context_args))

val ponytail_args = "{\"file\":\"" + clean_path + "\",\"mode\":\"audit\",\"format\":\"text\"}"
_expect_absence_marker_hidden(dispatch_tool_content("simple_ponytail", ponytail_args))
_expect_absence_marker_hidden(lower_handle_simple_ponytail("lower-absence-ponytail", ponytail_args))

val missing_ponytail_args = """{"file":"build/test/mcp_context_ponytail_dispatch/missing_ponytail.spl","mode":"audit","format":"text"}"""
_expect_absence_marker_hidden(dispatch_tool_content("simple_ponytail", missing_ponytail_args))
_expect_absence_marker_hidden(lower_handle_simple_ponytail("lower-missing-ponytail", missing_ponytail_args))
```

</details>

#### simple_ponytail

#### executes through the app MCP dispatcher and returns an audit report

- executes through the app MCP dispatcher and returns an audit report


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("executes through the app MCP dispatcher and returns an audit report")
val args = """{"file":"src/app/mcp/main_dispatch.spl","mode":"audit","format":"text"}"""
val response = dispatch_tool_content("simple_ponytail", args)
expect(response).to_contain("Ponytail Audit")
expect(response).to_contain("source: src/app/mcp/main_dispatch.spl")
```

</details>

#### simple_pipe

#### advertises one SPipe-linked front door for context and Ponytail

- advertises one SPipe-linked front door for context and Ponytail


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("advertises one SPipe-linked front door for context and Ponytail")
val response = lower_make_tools_list("\"lower-list-pipe\"")
expect(response).to_contain("\"name\":\"simple_pipe\"")
expect(response).to_contain("SPipe-linked codebase, context, and Ponytail surface")
```

</details>

#### routes context through the app MCP dispatcher

- routes context through the app MCP dispatcher


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("routes context through the app MCP dispatcher")
val args = """{"surface":"context","file":"src/app/mcp/main_dispatch.spl","target":"dispatch_tool","format":"text"}"""
val response = dispatch_tool_content("simple_pipe", args)
expect(response).to_contain("-- simple_context file=src/app/mcp/main_dispatch.spl --")
expect(response).to_contain("dispatch_tool")
```

</details>

#### routes Ponytail through lower MCP with mode=ponytail

- routes Ponytail through lower MCP with mode=ponytail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("routes Ponytail through lower MCP with mode=ponytail")
val args = """{"mode":"ponytail","file":"src/lib/nogc_async_mut/mcp/main_lazy.spl","format":"text"}"""
val response = lower_handle_simple_pipe("lower-pipe-ponytail", args)
expect(response).to_contain("Ponytail Audit")
expect(response).to_contain("source: src/lib/nogc_async_mut/mcp/main_lazy.spl")
```

</details>

#### reports the SPipe-linked surface without requiring a file

- reports the SPipe-linked surface without requiring a file


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("reports the SPipe-linked surface without requiring a file")
val response = dispatch_tool_content("simple_pipe", """{"surface":"spipe"}""")
expect(response).to_contain("simple_pipe")
expect(response).to_contain("spipe: linked")
expect(response).to_contain("surfaces: context, codebase, ponytail, search")
```

</details>

#### lower MCP

#### advertises simple_context and simple_ponytail through the lower MCP tools list

- advertises simple_context and simple_ponytail through the lower MCP tools list


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("advertises simple_context and simple_ponytail through the lower MCP tools list")
val response = lower_make_tools_list("\"lower-list-1\"")
expect(response).to_contain("\"id\":\"lower-list-1\"")
expect(response).to_contain("\"name\":\"simple_pipe\"")
expect(response).to_contain("\"name\":\"simple_context\"")
expect(response).to_contain("\"name\":\"simple_ponytail\"")
expect(response).to_contain("\"inputSchema\"")
expect(response).to_contain("\"Source file path; required except when sql=true and query is non-empty\"")
expect(response).to_contain("\"Mode: audit/review, simplification/simplify\"")
expect(response).to_contain("\"source_filter\"")
```

</details>

#### executes simple_context through the lower MCP handler

- executes simple_context through the lower MCP handler


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("executes simple_context through the lower MCP handler")
val args = """{"file":"src/lib/nogc_async_mut/mcp/main_lazy.spl","target":"handle_simple_context","format":"text"}"""
val response = lower_handle_simple_context("lower-context-1", args)
expect(response).to_contain("-- simple_context file=src/lib/nogc_async_mut/mcp/main_lazy.spl --")
expect(response).to_contain("--- Context Pack ---")
expect(response).to_contain("handle_simple_context")
```

</details>

#### executes simple_ponytail through the lower MCP handler

- executes simple_ponytail through the lower MCP handler


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("executes simple_ponytail through the lower MCP handler")
val args = """{"file":"src/lib/nogc_async_mut/mcp/main_lazy.spl","mode":"audit","format":"text"}"""
val response = lower_handle_simple_ponytail("lower-ponytail-1", args)
expect(response).to_contain("Ponytail Audit")
expect(response).to_contain("source: src/lib/nogc_async_mut/mcp/main_lazy.spl")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/llm_tooling_context_ponytail_mimic.md`
- **Plan:** `doc/03_plan/agent_tasks/llm_tooling_context_ponytail_mimic.md`
- **Design:** `doc/05_design/app/tools/llm_tooling_context_ponytail_mimic.md`
- **Research:** `doc/01_research/local/llm_tooling_context_ponytail_mimic.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2cf78a02eed71a02dd515fc84ba666ac5a398c3100e73fc0c2dc77f1867f6804`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2cf78a02eed71a02dd515fc84ba666ac5a398c3100e73fc0c2dc77f1867f6804`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2cf78a02eed71a02dd515fc84ba666ac5a398c3100e73fc0c2dc77f1867f6804`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/02_integration/app/mcp_context_ponytail_dispatch_spec.spl
mirror: doc/06_spec/02_integration/app/mcp_context_ponytail_dispatch_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/app/mcp_context_ponytail_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/app/mcp_context_ponytail_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/app/mcp_context_ponytail_dispatch_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/app/mcp_context_ponytail_dispatch_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes through the app MCP dispatcher and returns a context pack' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/mcp_context_ponytail_dispatch_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'executes source-less embedded SQL query through the app MCP dispatcher' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/app/mcp_context_ponytail_dispatch_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders MCP context and Ponytail absence without internal markers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
