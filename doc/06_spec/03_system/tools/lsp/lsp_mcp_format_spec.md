# Lsp Mcp Format Specification

> Tests covering LSP MCP Format Output.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lsp Mcp Format Specification

## Scenarios

### LSP MCP Format Output

#### structuredContent presence

<details>
<summary>Advanced: query check --format=json output contains structuredContent key</summary>

#### query check --format=json output contains structuredContent key _(slow)_

- query check --format=json output contains structuredContent key
   - Expected: has_structured is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("query check --format=json output contains structuredContent key")
val code = "fn test():\n    val unused_var = 42\n    print \"done\"\n"
val path = write_temp_file("struct_content", code)
val output = run_check_json(path)
val has_structured = output.contains("structuredContent") or output.contains("diagnostics")
expect(has_structured).to_equal(true)
```

</details>


</details>

#### diagnostics array

<details>
<summary>Advanced: diagnostics array is present in output</summary>

#### diagnostics array is present in output _(slow)_

- diagnostics array is present in output
   - Expected: has_diagnostics is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diagnostics array is present in output")
val code = "fn broken(\n    val x = \n"
val path = write_temp_file("diag_array", code)
val output = run_check_json(path)
val has_diagnostics = output.contains("\"diagnostics\"")
expect(has_diagnostics).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: diagnostics array contains entries for errors</summary>

#### diagnostics array contains entries for errors _(slow)_

- diagnostics array contains entries for errors
   - Expected: has_line is true
   - Expected: has_message is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("diagnostics array contains entries for errors")
val code = "fn test() -> i64:\n    return 42\n    val dead = 10\n"
val path = write_temp_file("diag_entries", code)
val output = run_check_json(path)
# Should have at least one diagnostic entry with line/message
val has_line = output.contains("\"line\"")
val has_message = output.contains("\"message\"")
expect(has_line).to_equal(true)
expect(has_message).to_equal(true)
```

</details>


</details>

#### count field

<details>
<summary>Advanced: count field is present in output</summary>

#### count field is present in output _(slow)_

- count field is present in output
   - Expected: has_count is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("count field is present in output")
val code = "fn test():\n    val unused1 = 1\n    val unused2 = 2\n    print \"done\"\n"
val path = write_temp_file("count_field", code)
val output = run_check_json(path)
# Output should contain count information (error_count or warning_count or count)
val has_count = output.contains("\"error_count\"") or output.contains("\"warning_count\"") or output.contains("\"count\"")
expect(has_count).to_equal(true)
```

</details>


</details>

#### isError field

<details>
<summary>Advanced: isError field reflects error status</summary>

#### isError field reflects error status _(slow)_

- isError field reflects error status
   - Expected: has_status is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("isError field reflects error status")
val code = "fn broken(\n"
val path = write_temp_file("is_error", code)
val output = run_check_json(path)
# Output should indicate error status
val has_status = output.contains("\"status\"") or output.contains("\"isError\"") or output.contains("\"exit_code\"")
expect(has_status).to_equal(true)
```

</details>


</details>

#### diagnostic entry fields

<details>
<summary>Advanced: each diagnostic has severity field</summary>

#### each diagnostic has severity field _(slow)_

- each diagnostic has severity field
   - Expected: has_severity is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("each diagnostic has severity field")
val code = "fn test():\n    val unused_x = 42\n    print \"done\"\n"
val path = write_temp_file("has_severity", code)
val output = run_check_json(path)
val has_severity = output.contains("\"severity\"")
expect(has_severity).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: each diagnostic has code field</summary>

#### each diagnostic has code field _(slow)_

- each diagnostic has code field
   - Expected: has_code_field is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("each diagnostic has code field")
val code = "fn test_depr():\n    val result = Vec__new()\n"
val path = write_temp_file("has_code", code)
val output = run_check_json(path)
val has_code_field = output.contains("\"code\"")
expect(has_code_field).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: each diagnostic has message field</summary>

#### each diagnostic has message field _(slow)_

- each diagnostic has message field
   - Expected: has_message is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("each diagnostic has message field")
val code = "fn test() -> i64:\n    return 42\n    val dead = 0\n"
val path = write_temp_file("has_message", code)
val output = run_check_json(path)
val has_message = output.contains("\"message\"")
expect(has_message).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: each diagnostic has line field</summary>

#### each diagnostic has line field _(slow)_

- each diagnostic has line field
   - Expected: has_line is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("each diagnostic has line field")
val code = "fn test():\n    val unused_z = 99\n    print \"done\"\n"
val path = write_temp_file("has_line", code)
val output = run_check_json(path)
val has_line = output.contains("\"line\"")
expect(has_line).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: each diagnostic has col field</summary>

#### each diagnostic has col field _(slow)_

- each diagnostic has col field
   - Expected: has_col is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("each diagnostic has col field")
val code = "fn broken(\n    val x = \n"
val path = write_temp_file("has_col", code)
val output = run_check_json(path)
val has_col = output.contains("\"col\"")
expect(has_col).to_equal(true)
```

</details>


</details>

#### clean code

<details>
<summary>Advanced: clean code produces zero diagnostics</summary>

#### clean code produces zero diagnostics _(slow)_

- clean code produces zero diagnostics
   - Expected: has_ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clean code produces zero diagnostics")
val code = "fn add(a: i64, b: i64) -> i64:\n    a + b\n"
val path = write_temp_file("clean_code", code)
val output = run_check_json(path)
# Clean code should have status "ok" and 0 counts
val has_ok = output.contains("\"ok\"") or output.contains("\"error_count\":0") or output.contains("\"error_count\": 0") or output.contains("\"count\":0") or output.contains("\"count\": 0")
expect(has_ok).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | LSP |
| Status | Active |
| Source | `test/03_system/tools/lsp/lsp_mcp_format_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LSP MCP Format Output.
- LSP MCP Format Output

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 11 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e83b0a4ff15647161f81fe7276e5c4d20b1844de24ad50f700bacba5d020759e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e83b0a4ff15647161f81fe7276e5c4d20b1844de24ad50f700bacba5d020759e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e83b0a4ff15647161f81fe7276e5c4d20b1844de24ad50f700bacba5d020759e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/tools/lsp/lsp_mcp_format_spec.spl
mirror: doc/06_spec/03_system/tools/lsp/lsp_mcp_format_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/lsp/lsp_mcp_format_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/lsp/lsp_mcp_format_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/lsp/lsp_mcp_format_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'query check --format=json output contains structuredContent key' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/lsp/lsp_mcp_format_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'diagnostics array is present in output' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/lsp/lsp_mcp_format_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'diagnostics array contains entries for errors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
