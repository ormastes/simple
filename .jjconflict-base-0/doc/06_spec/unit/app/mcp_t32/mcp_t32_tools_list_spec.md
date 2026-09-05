# Mcp T32 Tools List Specification

> Tests covering T32 MCP tools/list schema.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 Tools List Specification

## Scenarios

### T32 MCP tools/list schema

#### schema structure

#### generates valid schema with type object

- generates valid schema with type object


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates valid schema with type object")
val schema = make_tool_schema("t32_cmd_run", "Run command")
expect(schema).to_contain("\"type\":\"object\"")
```

</details>

#### includes properties field

- includes properties field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes properties field")
val schema = make_tool_schema("t32_cmd_run", "Run command")
expect(schema).to_contain("\"properties\":")
```

</details>

#### omits required when empty array

- omits required when empty array
   - Expected: not schema contains `"required"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("omits required when empty array")
# This is the KEY FIX for bug 5: tools with no required params
# must NOT emit "required":[] — that causes MCP client validation errors
val schema = make_tool_schema("t32_sessions_list", "List sessions")
expect(not schema.contains("\"required\"")).to_equal(true)
```

</details>

#### includes required when non-empty

- includes required when non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes required when non-empty")
val schema = make_tool_schema("t32_cmd_run", "Run command")
expect(schema).to_contain("\"required\":")
```

</details>

#### required contains correct param names

- required contains correct param names


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("required contains correct param names")
val schema = make_tool_schema("t32_session_open", "Open session")
expect(schema).to_contain("\"required\":[\"host\",\"port\"]")
```

</details>

#### tool object structure

#### includes name field

- includes name field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes name field")
val tool = make_tool_schema("t32_eval", "Evaluate expression")
expect(tool).to_contain("\"name\":\"t32_eval\"")
```

</details>

#### includes description field

- includes description field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes description field")
val tool = make_tool_schema("t32_eval", "Evaluate expression")
expect(tool).to_contain("\"description\":\"Evaluate expression\"")
```

</details>

#### includes inputSchema field

- includes inputSchema field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes inputSchema field")
val tool = make_tool_schema("t32_eval", "Evaluate expression")
expect(tool).to_contain("\"inputSchema\":")
```

</details>

#### includes annotations field

- includes annotations field


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes annotations field")
val tool = make_tool_schema("t32_eval", "Evaluate expression")
expect(tool).to_contain("\"annotations\":")
```

</details>

#### annotations correctness

#### read-only tools have readOnlyHint true

- read-only tools have readOnlyHint true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read-only tools have readOnlyHint true")
val read_only_tools = ["t32_sessions_list", "t32_field_get", "t32_eval", "t32_window_list", "t32_error_check", "t32_status_snapshot"]
for tool_name in read_only_tools:
    val tool = make_tool_schema(tool_name, "desc")
    expect(tool).to_contain("\"readOnlyHint\":true")
```

</details>

#### destructive tools have destructiveHint true

- destructive tools have destructiveHint true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("destructive tools have destructiveHint true")
val tool = make_tool_schema("t32_session_close", "Close session")
expect(tool).to_contain("\"destructiveHint\":true")
```

</details>

#### non-idempotent tools have idempotentHint false

- non-idempotent tools have idempotentHint false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("non-idempotent tools have idempotentHint false")
val non_idempotent = ["t32_cmd_run", "t32_cmm_run"]
for tool_name in non_idempotent:
    val tool = make_tool_schema(tool_name, "desc")
    expect(tool).to_contain("\"idempotentHint\":false")
```

</details>

#### specific tool schemas

#### t32_sessions_list has empty properties

- t32_sessions_list has empty properties


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_sessions_list has empty properties")
val tool = make_tool_schema("t32_sessions_list", "List sessions")
expect(tool).to_contain("\"properties\":{}")
```

</details>

#### t32_session_open requires host and port

- t32_session_open requires host and port


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_session_open requires host and port")
val tool = make_tool_schema("t32_session_open", "Open session")
expect(tool).to_contain("\"host\":")
expect(tool).to_contain("\"port\":")
expect(tool).to_contain("\"required\":[\"host\",\"port\"]")
```

</details>

#### t32_cmd_run requires command

- t32_cmd_run requires command


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_cmd_run requires command")
val tool = make_tool_schema("t32_cmd_run", "Run command")
expect(tool).to_contain("\"command\":")
expect(tool).to_contain("\"required\":[\"command\"]")
```

</details>

#### t32_eval requires expression

- t32_eval requires expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_eval requires expression")
val tool = make_tool_schema("t32_eval", "Evaluate")
expect(tool).to_contain("\"expression\":")
expect(tool).to_contain("\"required\":[\"expression\"]")
```

</details>

#### t32_error_check has empty properties and no required

- t32_error_check has empty properties and no required
   - Expected: not tool contains `"required"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_error_check has empty properties and no required")
val tool = make_tool_schema("t32_error_check", "Check errors")
expect(tool).to_contain("\"properties\":{}")
expect(not tool.contains("\"required\"")).to_equal(true)
```

</details>

#### t32_window_list has empty properties and no required

- t32_window_list has empty properties and no required
   - Expected: not tool contains `"required"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_window_list has empty properties and no required")
val tool = make_tool_schema("t32_window_list", "List windows")
expect(tool).to_contain("\"properties\":{}")
expect(not tool.contains("\"required\"")).to_equal(true)
```

</details>

#### t32_status_snapshot has empty properties and no required

- t32_status_snapshot has empty properties and no required
   - Expected: not tool contains `"required"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("t32_status_snapshot has empty properties and no required")
val tool = make_tool_schema("t32_status_snapshot", "Status")
expect(tool).to_contain("\"properties\":{}")
expect(not tool.contains("\"required\"")).to_equal(true)
```

</details>

#### JSON validity

#### tool schema has matching braces

- tool schema has matching braces
   - Expected: braces_balanced(tool) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tool schema has matching braces")
val tool = make_tool_schema("t32_cmd_run", "Run command")
expect(braces_balanced(tool)).to_equal(true)
```

</details>

#### tool schema has no trailing comma

- tool schema has no trailing comma
   - Expected: not tool contains `,}`
   - Expected: not tool contains `,]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tool schema has no trailing comma")
val tool = make_tool_schema("t32_eval", "Evaluate")
expect(not tool.contains(",}")).to_equal(true)
expect(not tool.contains(",]")).to_equal(true)
```

</details>

#### complete tools list wraps in array

- complete tools list wraps in array
   - Expected: braces_balanced(list) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("complete tools list wraps in array")
val list = build_tools_list()
expect(list).to_start_with("[")
expect(list).to_end_with("]")
expect(braces_balanced(list)).to_equal(true)
```

</details>

#### tools list contains all registered tools

- tools list contains all registered tools


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tools list contains all registered tools")
val list = build_tools_list()
expect(list).to_contain("t32_sessions_list")
expect(list).to_contain("t32_session_open")
expect(list).to_contain("t32_session_close")
expect(list).to_contain("t32_cmd_run")
expect(list).to_contain("t32_cmm_run")
expect(list).to_contain("t32_eval")
expect(list).to_contain("t32_error_check")
expect(list).to_contain("t32_field_get")
expect(list).to_contain("t32_window_list")
expect(list).to_contain("t32_status_snapshot")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_t32/mcp_t32_tools_list_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 MCP tools/list schema.
- T32 MCP tools/list schema

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
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

- Canonical SPipe generation for source `d929f6725b63914bfa3a611d53f2719c5ddf506c6d8309f524dbfb43a35db2f2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d929f6725b63914bfa3a611d53f2719c5ddf506c6d8309f524dbfb43a35db2f2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d929f6725b63914bfa3a611d53f2719c5ddf506c6d8309f524dbfb43a35db2f2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_t32/mcp_t32_tools_list_spec.spl
mirror: doc/06_spec/unit/app/mcp_t32/mcp_t32_tools_list_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_t32/mcp_t32_tools_list_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_t32/mcp_t32_tools_list_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_t32/mcp_t32_tools_list_spec.spl:199:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'generates valid schema with type object' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_tools_list_spec.spl:205:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes properties field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_t32/mcp_t32_tools_list_spec.spl:211:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'omits required when empty array' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
