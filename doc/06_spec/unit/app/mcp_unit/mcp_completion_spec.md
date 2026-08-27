# Mcp Completion Specification

> Tests covering MCP Completion Request, MCP Completion Response Format, MCP Context-Aware Completions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Completion Specification

## Scenarios

### MCP Completion Request

#### when requesting prompt completions

#### accepts completion request with ref/prompt

- accepts completion request with ref/prompt
   - Expected: params contains `ref/prompt`
   - Expected: params contains `language`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts completion request with ref/prompt")
val ref = jo2(jp("type", js("ref/prompt")), jp("name", js("code-review")))
val arg = jo2(jp("name", js("language")), jp("value", js("py")))
val params = jo2(jp("ref", ref), jp("argument", arg))
expect(params.contains("ref/prompt")).to_equal(true)
expect(params.contains("language")).to_equal(true)
```

</details>

#### handles ref/prompt reference type

- handles ref/prompt reference type
   - Expected: ref_type equals `ref/prompt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles ref/prompt reference type")
val ref = jo1(jp("type", js("ref/prompt")))
val ref_type = extract_json_string(ref, "type")
expect(ref_type).to_equal("ref/prompt")
```

</details>

#### builds completion params with argument value

- builds completion params with argument value
   - Expected: arg_value equals `py`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds completion params with argument value")
val arg = jo2(jp("name", js("language")), jp("value", js("py")))
val arg_value = extract_json_string(arg, "value")
expect(arg_value).to_equal("py")
```

</details>

#### when requesting resource completions

#### handles ref/resource reference type

- handles ref/resource reference type
   - Expected: ref_type equals `ref/resource`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles ref/resource reference type")
val ref = jo2(jp("type", js("ref/resource")), jp("uri", js("file:///*")))
val ref_type = extract_json_string(ref, "type")
expect(ref_type).to_equal("ref/resource")
```

</details>

#### includes uri in resource ref

- includes uri in resource ref
   - Expected: ref contains `bugdb://`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes uri in resource ref")
val ref = jo2(jp("type", js("ref/resource")), jp("uri", js("bugdb:///*")))
expect(ref.contains("bugdb://")).to_equal(true)
```

</details>

### MCP Completion Response Format

#### when building completion response

#### includes values array

- includes values array
   - Expected: response contains `values`
   - Expected: response contains `python`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes values array")
val values = "[" + js("python") + "," + js("perl") + "]"
val completion = jo3(jp("values", values), jp("total", "2"), jp("hasMore", "false"))
val result = jo1(jp("completion", completion))
val response = make_result_response("1", result)
expect(response.contains("values")).to_equal(true)
expect(response.contains("python")).to_equal(true)
```

</details>

#### includes total count

- includes total count
   - Expected: response contains `"total":5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes total count")
val completion = jo3(jp("values", "[]"), jp("total", "5"), jp("hasMore", "false"))
val result = jo1(jp("completion", completion))
val response = make_result_response("1", result)
expect(response.contains("\"total\":5")).to_equal(true)
```

</details>

#### includes hasMore flag

- includes hasMore flag
   - Expected: response contains `"hasMore":true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes hasMore flag")
val completion = jo3(jp("values", "[]"), jp("total", "150"), jp("hasMore", "true"))
val result = jo1(jp("completion", completion))
val response = make_result_response("1", result)
expect(response.contains("\"hasMore\":true")).to_equal(true)
```

</details>

#### values array has max 100 items

- values array has max 100 items
   - Expected: actual_items <= max_items is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("values array has max 100 items")
val max_items = 100
val actual_items = 5
expect(actual_items <= max_items).to_equal(true)
```

</details>

#### when no completions available

#### returns empty values array

- returns empty values array
   - Expected: response contains `"values":[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty values array")
val completion = jo3(jp("values", "[]"), jp("total", "0"), jp("hasMore", "false"))
val result = jo1(jp("completion", completion))
val response = make_result_response("1", result)
expect(response.contains("\"values\":[]")).to_equal(true)
```

</details>

#### returns zero total

- returns zero total
   - Expected: completion contains `"total":0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns zero total")
val completion = jo3(jp("values", "[]"), jp("total", "0"), jp("hasMore", "false"))
expect(completion.contains("\"total\":0")).to_equal(true)
```

</details>

#### returns hasMore as false

- returns hasMore as false
   - Expected: completion contains `"hasMore":false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns hasMore as false")
val completion = jo3(jp("values", "[]"), jp("total", "0"), jp("hasMore", "false"))
expect(completion.contains("\"hasMore\":false")).to_equal(true)
```

</details>

### MCP Context-Aware Completions

#### when context arguments provided

#### accepts context parameter in params

- accepts context parameter in params
   - Expected: params contains `context`
   - Expected: params contains `python`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts context parameter in params")
val context_arg = jo1(jp("language", js("python")))
val arg = jo2(jp("name", js("style")), jp("value", js("d")))
val params = jo3(jp("ref", jo1(jp("type", js("ref/prompt")))), jp("argument", arg), jp("context", context_arg))
expect(params.contains("context")).to_equal(true)
expect(params.contains("python")).to_equal(true)
```

</details>

#### extracts context values

- extracts context values
   - Expected: lang equals `python`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts context values")
val context_arg = jo1(jp("language", js("python")))
val lang = extract_json_string(context_arg, "language")
expect(lang).to_equal("python")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/mcp_completion_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP Completion Request, MCP Completion Response Format, MCP Context-Aware Completions.
- MCP Completion Request
- MCP Completion Response Format
- MCP Context-Aware Completions

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

- Canonical SPipe generation for source `e10e606aa3752652ec75633a3da18712a003ffe2cb14dd062514e40d72efd0f8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e10e606aa3752652ec75633a3da18712a003ffe2cb14dd062514e40d72efd0f8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e10e606aa3752652ec75633a3da18712a003ffe2cb14dd062514e40d72efd0f8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/mcp_completion_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_completion_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_completion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_completion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_completion_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts completion request with ref/prompt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_completion_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles ref/prompt reference type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_completion_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds completion params with argument value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
