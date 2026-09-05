# mcp_lsp_tools_spec

> An MCP client that calls one of the ten LSP tools without the parameter the

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mcp_lsp_tools_spec

An MCP client that calls one of the ten LSP tools without the parameter the

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/mcp_lsp_tools_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

An MCP client that calls one of the ten LSP tools without the parameter the
    tool needs must get a JSON-RPC invalid-params error naming the parameter,
    not a silently-empty success. These examples drive the real dispatcher, so
    they also prove each tool name is still wired to a handler.

## Scenarios

### Tier 4 LSP tools reject a request that omits a required parameter

#### simple_signature_help reports the missing file parameter

- simple_signature_help reports the missing file parameter
- Call the live dispatcher for simple_signature_help with an empty body
- Expect an invalid-params error naming 'file'


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_signature_help reports the missing file parameter")
step("Call the live dispatcher for simple_signature_help with an empty body")
val out = dispatch_tool("t1", "simple_signature_help", "{}")
step("Expect an invalid-params error naming 'file'")
expect(out).to_contain("-32602")
expect(out).to_contain(missing_message("file"))
expect(out).to_contain("\"isError\":true")
```

</details>

#### simple_rename reports the missing file parameter

- simple_rename reports the missing file parameter
- Call the live dispatcher for simple_rename with an empty body


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_rename reports the missing file parameter")
step("Call the live dispatcher for simple_rename with an empty body")
val out = dispatch_tool("t2", "simple_rename", "{}")
expect(out).to_contain("-32602")
expect(out).to_contain(missing_message("file"))
```

</details>

#### simple_rename still rejects when only the new name is absent

- simple_rename still rejects when only the new name is absent
- Supply file and line but omit new_name, the destructive parameter
- A rename with no target name must never reach the CLI bridge


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_rename still rejects when only the new name is absent")
step("Supply file and line but omit new_name, the destructive parameter")
val out = dispatch_tool("t3", "simple_rename",
    "{\"file\":\"src/app/cli/main.spl\",\"line\":\"10\"}")
step("A rename with no target name must never reach the CLI bridge")
expect(out).to_contain("-32602")
expect(out).to_contain(missing_message("new_name"))
```

</details>

#### simple_code_actions reports the missing file parameter

- simple_code_actions reports the missing file parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_code_actions reports the missing file parameter")
val out = dispatch_tool("t4", "simple_code_actions", "{}")
expect(out).to_contain(missing_message("file"))
```

</details>

#### simple_workspace_symbols reports the missing query parameter

- simple_workspace_symbols reports the missing query parameter
- This tool is query-driven, not file-driven, so it names 'query'


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_workspace_symbols reports the missing query parameter")
step("This tool is query-driven, not file-driven, so it names 'query'")
val out = dispatch_tool("t5", "simple_workspace_symbols", "{}")
expect(out).to_contain(missing_message("query"))
```

</details>

#### simple_call_hierarchy reports the missing file parameter

- simple_call_hierarchy reports the missing file parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_call_hierarchy reports the missing file parameter")
val out = dispatch_tool("t6", "simple_call_hierarchy", "{}")
expect(out).to_contain(missing_message("file"))
```

</details>

#### simple_type_hierarchy reports the missing file parameter

- simple_type_hierarchy reports the missing file parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_type_hierarchy reports the missing file parameter")
val out = dispatch_tool("t7", "simple_type_hierarchy", "{}")
expect(out).to_contain(missing_message("file"))
```

</details>

#### simple_semantic_tokens reports the missing file parameter

- simple_semantic_tokens reports the missing file parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_semantic_tokens reports the missing file parameter")
val out = dispatch_tool("t8", "simple_semantic_tokens", "{}")
expect(out).to_contain(missing_message("file"))
```

</details>

#### simple_inlay_hints reports the missing file parameter

- simple_inlay_hints reports the missing file parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_inlay_hints reports the missing file parameter")
val out = dispatch_tool("t9", "simple_inlay_hints", "{}")
expect(out).to_contain(missing_message("file"))
```

</details>

#### simple_selection_range reports the missing file parameter

- simple_selection_range reports the missing file parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_selection_range reports the missing file parameter")
val out = dispatch_tool("t10", "simple_selection_range", "{}")
expect(out).to_contain(missing_message("file"))
```

</details>

#### simple_document_formatting reports the missing file parameter

- simple_document_formatting reports the missing file parameter
- Formatting rewrites a file, so an unnamed target must be refused


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_document_formatting reports the missing file parameter")
step("Formatting rewrites a file, so an unnamed target must be refused")
val out = dispatch_tool("t11", "simple_document_formatting", "{}")
expect(out).to_contain(missing_message("file"))
```

</details>

### Every Tier 4 tool holds the same contract (generalization)

#### no Tier 4 tool accepts an empty request body

- no Tier 4 tool accepts an empty request body
- Dispatch every Tier 4 tool name with an empty body
- Require an invalid-params error rather than a success result
   - Expected: offenders equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no Tier 4 tool accepts an empty request body")
step("Dispatch every Tier 4 tool name with an empty body")
val tools = tier4_tool_names()
var offenders = ""
var i = 0i64
while i < tools.len():
    val tool = tools[i]
    val out = dispatch_tool("g" + str(i), tool, "{}")
    step("Require an invalid-params error rather than a success result")
    if not out.contains("-32602"):
        offenders = offenders + " " + tool
    i = i + 1i64
expect(offenders).to_equal("")
```

</details>

#### every Tier 4 tool names the parameter it is missing

- every Tier 4 tool names the parameter it is missing
- An error that does not say WHICH parameter is unactionable for a client
   - Expected: offenders equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every Tier 4 tool names the parameter it is missing")
step("An error that does not say WHICH parameter is unactionable for a client")
val tools = tier4_tool_names()
var offenders = ""
var i = 0i64
while i < tools.len():
    val tool = tools[i]
    val out = dispatch_tool("m" + str(i), tool, "{}")
    if not out.contains(missing_message(tier4_missing_param(tool))):
        offenders = offenders + " " + tool
    i = i + 1i64
expect(offenders).to_equal("")
```

</details>

#### every Tier 4 tool echoes the request id it was given

- every Tier 4 tool echoes the request id it was given
- Correlating a response to its request is the JSON-RPC envelope contract
   - Expected: offenders equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every Tier 4 tool echoes the request id it was given")
step("Correlating a response to its request is the JSON-RPC envelope contract")
val tools = tier4_tool_names()
var offenders = ""
var i = 0i64
while i < tools.len():
    val tool = tools[i]
    val request_id = "echo" + str(i)
    val out = dispatch_tool(request_id, tool, "{}")
    if not out.contains(request_id):
        offenders = offenders + " " + tool
    i = i + 1i64
expect(offenders).to_equal("")
```

</details>

#### every Tier 4 tool is still wired into the dispatcher

- every Tier 4 tool is still wired into the dispatcher
- An unwired name would fall through and never produce a tool error
   - Expected: wired equals `10i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every Tier 4 tool is still wired into the dispatcher")
step("An unwired name would fall through and never produce a tool error")
val tools = tier4_tool_names()
var wired = 0i64
var i = 0i64
while i < tools.len():
    val out = dispatch_tool("w" + str(i), tools[i], "{}")
    if out.contains("\"jsonrpc\":\"2.0\"") and out.contains("-32602"):
        wired = wired + 1i64
    i = i + 1i64
expect(wired).to_equal(10i64)
```

</details>

### A complete Tier 4 request reaches the real query bridge

#### simple_selection_range returns a real bridged result, not an error

- simple_selection_range returns a real bridged result, not an error
- Supply both required parameters for a file that exists
- The handler stamps the tool name and the bridge's exit code
- A success envelope carries structured rawText and sets no isError flag
   - Expected: out does not contain `"isError":true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_selection_range returns a real bridged result, not an error")
step("Supply both required parameters for a file that exists")
val out = handle_simple_selection_range("r1",
    "{\"file\":\"src/app/cli/main.spl\",\"line\":\"10\"}")
step("The handler stamps the tool name and the bridge's exit code")
expect(out).to_contain("-- simple_selection_range (exit: ")
step("A success envelope carries structured rawText and sets no isError flag")
expect(out).to_contain("\"rawText\"")
expect(out.contains("\"isError\":true")).to_equal(false)
```

</details>

#### simple_semantic_tokens returns a real bridged result, not an error

- simple_semantic_tokens returns a real bridged result, not an error
   - Expected: out does not contain `"isError":true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simple_semantic_tokens returns a real bridged result, not an error")
val out = handle_simple_semantic_tokens("r2",
    "{\"file\":\"src/app/cli/main.spl\"}")
expect(out).to_contain("-- simple_semantic_tokens (exit: ")
expect(out).to_contain("\"rawText\"")
expect(out.contains("\"isError\":true")).to_equal(false)
```

</details>

#### a bridged result carries the query output, not just the header

- a bridged result carries the query output, not just the header
- The formatted result is header plus the CLI's own output
- Header alone is about 40 characters; a real bridged body is far longer
   - Expected: out.len() > 200i64 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("a bridged result carries the query output, not just the header")
step("The formatted result is header plus the CLI's own output")
val out = handle_simple_selection_range("r3",
    "{\"file\":\"src/app/cli/main.spl\",\"line\":\"10\"}")
step("Header alone is about 40 characters; a real bridged body is far longer")
expect(out.len() > 200i64).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `3614e8d9573c02456930e7c96680b04f234acb5bf04430c6f309f0df8d5d85f8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3614e8d9573c02456930e7c96680b04f234acb5bf04430c6f309f0df8d5d85f8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3614e8d9573c02456930e7c96680b04f234acb5bf04430c6f309f0df8d5d85f8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/mcp_lsp_tools_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_lsp_tools_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_lsp_tools_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_lsp_tools_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_lsp_tools_spec.spl:84:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'simple_signature_help reports the missing file parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_lsp_tools_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'simple_rename reports the missing file parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_lsp_tools_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'simple_rename still rejects when only the new name is absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
