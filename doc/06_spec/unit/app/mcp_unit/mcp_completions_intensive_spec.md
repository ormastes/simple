# MCP Completions Intensive

> This spec replaces the skip-only completions placeholder with executable coverage for MCP completion protocol handling and the `simple_completions` tool surface.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Completions Intensive

This spec replaces the skip-only completions placeholder with executable coverage for MCP completion protocol handling and the `simple_completions` tool surface.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/unit/app/mcp_unit/mcp_completions_intensive_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This spec replaces the skip-only completions placeholder with executable
coverage for MCP completion protocol handling and the `simple_completions`
tool surface.

The covered contract is:

- app and lower MCP protocol handlers return completion envelopes,
- completion suggestions cover common prompt/resource argument names,
- `simple_completions` validates `file` and `line`,
- completion schemas expose `file`, `line`, `column`, and `prefix`,
- completion tools are advertised as read-only query tools.

## Syntax

The spec reads MCP completion sources through the standard file facade and
checks stable protocol/tool markers without invoking shell-backed completions.

## Examples

```spl
use std.spec.step

val source = file_read_text("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("fn handle_simple_completions(id: text, body: text) -> text:")
```

## Scenarios

### Mcp Completions Intensive

#### app protocol completion handler returns completion envelope

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- app protocol completion handler returns completion envelope


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("app protocol completion handler returns completion envelope")
val source = file_read_text("src/app/mcp/main_lazy_protocol.spl") ?? ""
expect(source).to_contain("fn handle_completion_req(id: text, body: text) -> text:")
expect(source).to_contain("completion = completion + jp(\"values\", values)")
expect(source).to_contain("completion = completion + \",\" + jp(\"total\", str(total))")
expect(source).to_contain("completion = completion + \",\" + jp(\"hasMore\", \"false\")")
expect(source).to_contain("val result = jo1(jp(\"completion\", completion))")
```

</details>

#### lower protocol completion handler offers standard argument suggestions

- lower protocol completion handler offers standard argument suggestions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lower protocol completion handler offers standard argument suggestions")
val source = file_read_text("src/lib/nogc_async_mut/mcp/lazy_protocol_resources.spl") ?? ""
expect(source).to_contain("fn handle_completion_req(id: text, body: text) -> text:")
expect(source).to_contain("if arg_name == \"path\":")
expect(source).to_contain("js(\"src/\")")
expect(source).to_contain("elif arg_name == \"target_type\":")
expect(source).to_contain("js(\"interpreter\")")
```

</details>

#### simple_completions validates required coordinates

- simple_completions validates required coordinates


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_completions validates required coordinates")
val source = file_read_text("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("fn handle_simple_completions(id: text, body: text) -> text:")
expect(source).to_contain("val file = extract_field(body, \"file\")")
expect(source).to_contain("val line = extract_field(body, \"line\")")
expect(source).to_contain("Missing required parameter: file")
expect(source).to_contain("Missing required parameter: line")
```

</details>

#### simple_completions builds query command with optional column and prefix

- simple_completions builds query command with optional column and prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_completions builds query command with optional column and prefix")
val source = file_read_text("src/lib/nogc_async_mut/mcp/main_lazy_query_tools.spl") ?? ""
expect(source).to_contain("query completions \" + file + \" \" + line")
expect(source).to_contain("if column != \"\":")
expect(source).to_contain("cmd = cmd + \" \" + column")
expect(source).to_contain("if prefix != \"\":")
expect(source).to_contain("cmd = cmd + \" --prefix \" + prefix")
```

</details>

#### completion schemas advertise arguments and read-only metadata

- completion schemas advertise arguments and read-only metadata


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("completion schemas advertise arguments and read-only metadata")
val schema = file_read_text("src/lib/nogc_async_mut/mcp/lazy_protocol_schemas.spl") ?? ""
val dispatch = file_read_text("src/lib/nogc_async_mut/mcp/main_lazy.spl") ?? ""
expect(schema).to_contain("make_tool_schema(name: \"simple_completions\"")
expect(schema).to_contain("elif name == \"simple_completions\":")
expect(schema).to_contain("jp(\"prefix\", jo2(jp(\"type\", js(\"string\"))")
expect(schema).to_contain("req = \"[\" + js(\"file\") + \",\" + js(\"line\") + \"]\"")
expect(schema).to_contain("name == \"simple_definition\" or name == \"simple_references\" or name == \"simple_hover\" or name == \"simple_completions\"")
expect(dispatch).to_contain("elif tool_name == \"simple_completions\":")
expect(dispatch).to_contain("return handle_simple_completions(id, body)")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `6a83f0b6a9a77cbda5c4f39d37fab96ca0be03be2a2f122d015e5c671d5aa7bc`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6a83f0b6a9a77cbda5c4f39d37fab96ca0be03be2a2f122d015e5c671d5aa7bc`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6a83f0b6a9a77cbda5c4f39d37fab96ca0be03be2a2f122d015e5c671d5aa7bc`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/mcp_completions_intensive_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_completions_intensive_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_completions_intensive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_completions_intensive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_completions_intensive_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'app protocol completion handler returns completion envelope' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_completions_intensive_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'lower protocol completion handler offers standard argument suggestions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_completions_intensive_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'simple_completions validates required coordinates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
