# MCP Library Handler Registry

> Tests the MCP handler registry including tool handler registration, lookup by method name, and dispatch to registered handlers. Verifies that the registry correctly maps tool names to handler functions with proper parameter passing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Library Handler Registry

Tests the MCP handler registry including tool handler registration, lookup by method name, and dispatch to registered handlers. Verifies that the registry correctly maps tool names to handler functions with proper parameter passing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | In Progress |
| Source | `test/feature/lib/mcp/handler_registry_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the MCP handler registry including tool handler registration, lookup by
method name, and dispatch to registered handlers. Verifies that the registry
correctly maps tool names to handler functions with proper parameter passing.

## Scenarios

### MCP Library - Handler Registry

#### registers and finds tool handler

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- registers and finds tool handler
   - Expected: found.name equals `test_tool`
   - Expected: found.handler_module equals `app.handlers`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("registers and finds tool handler")
val handler = create_tool_handler(
    "test_tool",
    "Test tool",
    "{}",
    "app.handlers",
    "handle_test"
)
register_tool_handler(handler)

val found = find_tool_handler("test_tool")
expect(found.name).to_equal("test_tool")
expect(found.handler_module).to_equal("app.handlers")
```

</details>

#### returns empty handler for unknown tool

- returns empty handler for unknown tool
   - Expected: found.name equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns empty handler for unknown tool")
val found = find_tool_handler("unknown")
expect(found.name).to_equal("")
```

</details>

#### registers and finds resource handler

- registers and finds resource handler
   - Expected: found.uri_pattern equals `file://`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("registers and finds resource handler")
val handler = create_resource_handler(
    "file://",
    "app.resources",
    "handle_file"
)
register_resource_handler(handler)

val found = find_resource_handler("file:///path/to/file")
expect(found.uri_pattern).to_equal("file://")
```

</details>

#### creates tool handler with schema

- creates tool handler with schema
   - Expected: handler.name equals `t1`
   - Expected: handler.description equals `Tool 1`
   - Expected: handler.handler_fn equals `func`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("creates tool handler with schema")
val handler = create_tool_handler("t1", "Tool 1", "{}", "mod", "func")
expect(handler.name).to_equal("t1")
expect(handler.description).to_equal("Tool 1")
expect(handler.handler_fn).to_equal("func")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5622087ae9f2a318204c6a88bb50bc5fd9e94bfe424d45e3763b273a6ec2b021`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5622087ae9f2a318204c6a88bb50bc5fd9e94bfe424d45e3763b273a6ec2b021`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5622087ae9f2a318204c6a88bb50bc5fd9e94bfe424d45e3763b273a6ec2b021`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/lib/mcp/handler_registry_spec.spl
mirror: doc/06_spec/feature/lib/mcp/handler_registry_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/lib/mcp/handler_registry_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/lib/mcp/handler_registry_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/lib/mcp/handler_registry_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers and finds tool handler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/lib/mcp/handler_registry_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns empty handler for unknown tool' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/lib/mcp/handler_registry_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'registers and finds resource handler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
