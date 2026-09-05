# MCP Prompts Compiled

> This spec replaces the skip-only prompt placeholder with executable coverage for compiled MCP prompt list/get handlers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Prompts Compiled

This spec replaces the skip-only prompt placeholder with executable coverage for compiled MCP prompt list/get handlers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/unit/app/mcp_unit/prompts_compiled_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This spec replaces the skip-only prompt placeholder with executable coverage for
compiled MCP prompt list/get handlers.

The covered contract is:

- app MCP routes `prompts/list` and `prompts/get` from the main server loop,
- app prompt handlers expose prompt metadata and prompt responses,
- lower lazy MCP prompt handlers expose `analyze-file` and `generate-tests`,
- prompt responses use MCP message content envelopes.

## Syntax

The spec reads MCP prompt source files through the standard file facade and
checks stable handler markers without executing server loops.

## Examples

```spl
use std.spec.step

val source = file_read_text("src/app/mcp/main_lazy_protocol.spl") ?? ""
expect(source).to_contain("fn handle_prompts_list(id: text) -> text:")
```

## Scenarios

### Prompts Ext

#### app MCP main routes prompt list and prompt get methods

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- app MCP main routes prompt list and prompt get methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("app MCP main routes prompt list and prompt get methods")
val source = file_read_text("src/app/mcp/main.spl") ?? ""
expect(source).to_contain("elif has_method(msg, \"prompts/list\"):")
expect(source).to_contain("response = handle_prompts_list(id)")
expect(source).to_contain("elif has_method(msg, \"prompts/get\"):")
expect(source).to_contain("response = handle_prompts_get(id, prompt_name, msg)")
```

</details>

#### app prompt protocol exposes analyze and test prompts

- app prompt protocol exposes analyze and test prompts


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("app prompt protocol exposes analyze and test prompts")
val source = file_read_text("src/app/mcp/main_lazy_protocol.spl") ?? ""
expect(source).to_contain("fn handle_prompts_list(id: text) -> text:")
expect(source).to_contain("make_prompt_json(\"analyze-file\"")
expect(source).to_contain("make_prompt_json(\"generate-tests\"")
expect(source).to_contain("make_prompt_arg(\"path\", \"Path to file\", true)")
```

</details>

#### app prompt get returns prompt response envelopes

- app prompt get returns prompt response envelopes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("app prompt get returns prompt response envelopes")
val source = file_read_text("src/app/mcp/main_lazy_protocol.spl") ?? ""
expect(source).to_contain("fn handle_prompts_get(id: text, prompt_name: text, body: text) -> text:")
expect(source).to_contain("return make_prompt_response(id, \"Analyze file\", content)")
expect(source).to_contain("return make_prompt_response(id, \"Generate tests\", content)")
expect(source).to_contain("make_error(id, -32601, \"Unknown prompt: \" + prompt_name)")
```

</details>

#### lower MCP lazy prompt resources expose the same basic prompts

- lower MCP lazy prompt resources expose the same basic prompts


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lower MCP lazy prompt resources expose the same basic prompts")
val source = file_read_text("src/lib/nogc_async_mut/mcp/lazy_protocol_resources.spl") ?? ""
expect(source).to_contain("fn handle_prompts_list(id: text) -> text:")
expect(source).to_contain("make_prompt_json(name: \"analyze-file\"")
expect(source).to_contain("make_prompt_json(name: \"generate-tests\"")
expect(source).to_contain("make_prompt_arg(name: \"path\", desc: \"Path to file\", required: true)")
```

</details>

#### lower MCP prompt responses use message content envelopes

- lower MCP prompt responses use message content envelopes


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lower MCP prompt responses use message content envelopes")
val source = file_read_text("src/lib/nogc_async_mut/mcp/lazy_protocol_resources.spl") ?? ""
expect(source).to_contain("fn make_prompt_response(id: text, description: text, user_content: text) -> text:")
expect(source).to_contain("jp(\"messages\", \"[\" + msg + \"]\")")
expect(source).to_contain("jp(\"role\", js(\"user\"))")
expect(source).to_contain("jp(\"content\", content_obj)")
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

- Canonical SPipe generation for source `81dfa1a28ade57323439a316fc134426dc20568a6f967e4cfcae81f68bd90842`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `81dfa1a28ade57323439a316fc134426dc20568a6f967e4cfcae81f68bd90842`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `81dfa1a28ade57323439a316fc134426dc20568a6f967e4cfcae81f68bd90842`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/prompts_compiled_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/prompts_compiled_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/prompts_compiled_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/prompts_compiled_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/prompts_compiled_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'app MCP main routes prompt list and prompt get methods' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/prompts_compiled_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'app prompt protocol exposes analyze and test prompts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/prompts_compiled_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'app prompt get returns prompt response envelopes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
