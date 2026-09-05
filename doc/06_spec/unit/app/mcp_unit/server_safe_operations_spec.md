# Server Safe Operations Specification

> Tests covering Server Safe Operations, safe_read_resource, safe_execute_tool, Parameter Extraction.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Server Safe Operations Specification

## Scenarios

### Server Safe Operations

### safe_read_resource

#### handles validation error

- handles validation error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles validation error")
val validator = input_validator()
val result = validator.validate_uri("")
match result:
    case nil: expect(false).to_equal(true)
    case err: expect(err.message.contains("empty")).to_equal(true)
```

</details>

#### handles resource not found

- handles resource not found
   - Expected: response contains `Resource not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles resource not found")
val response = make_error_response("1", -32001, "Resource not found")
expect(response.contains("Resource not found")).to_equal(true)
```

</details>

#### successfully reads resource

- successfully reads resource
   - Expected: response contains `file data`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("successfully reads resource")
val response = make_result_response("1", jo1(jp("content", js("file data"))))
expect(response.contains("file data")).to_equal(true)
```

</details>

#### extracts uri parameter

- extracts uri parameter
   - Expected: uri equals `file:///test.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts uri parameter")
val params = jo1(jp("uri", js("file:///test.spl")))
val uri = extract_json_string(params, "uri")
expect(uri).to_equal("file:///test.spl")
```

</details>

#### handles missing uri parameter

- handles missing uri parameter
   - Expected: uri equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles missing uri parameter")
val params = jo1(jp("other", js("value")))
val uri = extract_json_string(params, "uri")
expect(uri).to_equal("")
```

</details>

### safe_execute_tool

#### handles validation error

- handles validation error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles validation error")
val validator = input_validator()
val result = validator.validate_tool_name("")
match result:
    case nil: expect(false).to_equal(true)
    case err: expect(err.message.contains("empty")).to_equal(true)
```

</details>

#### handles execution error

- handles execution error
   - Expected: response contains `Tool execution failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles execution error")
val response = make_error_response("1", -32002, "Tool execution failed")
expect(response.contains("Tool execution failed")).to_equal(true)
```

</details>

#### successfully executes tool

- successfully executes tool
   - Expected: response contains `Tool output data`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("successfully executes tool")
val response = make_tool_result("1", "Tool output data")
expect(response.contains("Tool output data")).to_equal(true)
```

</details>

#### extracts name parameter

- extracts name parameter
   - Expected: name equals `read_code`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts name parameter")
val params = jo1(jp("name", js("read_code")))
val name = extract_json_string(params, "name")
expect(name).to_equal("read_code")
```

</details>

#### handles missing name parameter

- handles missing name parameter
   - Expected: name equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles missing name parameter")
val params = jo1(jp("other", js("value")))
val name = extract_json_string(params, "name")
expect(name).to_equal("")
```

</details>

#### extracts arguments parameter

- extracts arguments parameter
   - Expected: args contains `path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts arguments parameter")
val params = jo2(jp("name", js("read_code")), jp("arguments", js("path=/test.spl")))
val args = extract_json_string(params, "arguments")
expect(args.contains("path")).to_equal(true)
```

</details>

#### handles missing arguments parameter

- handles missing arguments parameter
   - Expected: args equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles missing arguments parameter")
val params = jo1(jp("name", js("read_code")))
val args = extract_json_string(params, "arguments")
expect(args).to_equal("")
```

</details>

### Parameter Extraction

#### extracts all required parameters

- extracts all required parameters
   - Expected: name equals `read_code`
   - Expected: uri equals `file:///test.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts all required parameters")
val params = jo2(jp("name", js("read_code")), jp("uri", js("file:///test.spl")))
val name = extract_json_string(params, "name")
val uri = extract_json_string(params, "uri")
expect(name).to_equal("read_code")
expect(uri).to_equal("file:///test.spl")
```

</details>

#### handles partial parameter set

- handles partial parameter set
   - Expected: name equals `read_code`
   - Expected: uri equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles partial parameter set")
val params = jo1(jp("name", js("read_code")))
val name = extract_json_string(params, "name")
val uri = extract_json_string(params, "uri")
expect(name).to_equal("read_code")
expect(uri).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/server_safe_operations_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Server Safe Operations, safe_read_resource, safe_execute_tool, Parameter Extraction.
- Server Safe Operations
- safe_read_resource
- safe_execute_tool
- Parameter Extraction

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `eaee20b38f6897c68d4bd8b90567005b39afb1327b34c0b4dfb752ede8ead076`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eaee20b38f6897c68d4bd8b90567005b39afb1327b34c0b4dfb752ede8ead076`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eaee20b38f6897c68d4bd8b90567005b39afb1327b34c0b4dfb752ede8ead076`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/server_safe_operations_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/server_safe_operations_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/server_safe_operations_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/server_safe_operations_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/server_safe_operations_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles validation error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/server_safe_operations_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles resource not found' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/server_safe_operations_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'successfully reads resource' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
