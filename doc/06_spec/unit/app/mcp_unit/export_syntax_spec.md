# Export Syntax Specification

> Tests covering MCP module export syntax.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Export Syntax Specification

## Scenarios

### MCP module export syntax

<details>
<summary>Advanced: can import from mcp helpers</summary>

#### can import from mcp helpers _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- can import from mcp helpers
   - Expected: response contains `jsonrpc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can import from mcp helpers")
val response = make_result_response("1", jo1(jp("status", js("ok"))))
expect(response.contains("jsonrpc")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: can access protocol types from helpers</summary>

#### can access protocol types from helpers _(slow)_

- can access protocol types from helpers
   - Expected: extracted equals `initialize`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can access protocol types from helpers")
val method_name = "initialize"
val req = jo1(jp("method", js(method_name)))
val extracted = extract_json_string(req, "method")
expect(extracted).to_equal("initialize")
```

</details>


</details>

<details>
<summary>Advanced: can build JSON objects</summary>

#### can build JSON objects _(slow)_

- can build JSON objects
   - Expected: obj contains `key1`
   - Expected: obj contains `key2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can build JSON objects")
val obj = jo2(jp("key1", js("value1")), jp("key2", js("value2")))
expect(obj.contains("key1")).to_equal(true)
expect(obj.contains("key2")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: can use LB and RB helpers</summary>

#### can use LB and RB helpers _(slow)_

- can use LB and RB helpers
   - Expected: json contains `test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can use LB and RB helpers")
val json = LB() + jp("test", js("value")) + RB()
expect(json.contains("test")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/export_syntax_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP module export syntax.
- MCP module export syntax

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
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

- Canonical SPipe generation for source `68bff730d4a7be7a9379a1b7ec144407559c15a1d32af0069075ae79279aaea3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `68bff730d4a7be7a9379a1b7ec144407559c15a1d32af0069075ae79279aaea3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `68bff730d4a7be7a9379a1b7ec144407559c15a1d32af0069075ae79279aaea3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/app/mcp_unit/export_syntax_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/export_syntax_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/export_syntax_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/export_syntax_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/export_syntax_spec.spl:19:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can import from mcp helpers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/mcp_unit/export_syntax_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can import from mcp helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/export_syntax_spec.spl:25:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can access protocol types from helpers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/mcp_unit/export_syntax_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can access protocol types from helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/export_syntax_spec.spl:33:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can build JSON objects' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/unit/app/mcp_unit/export_syntax_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can build JSON objects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/export_syntax_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can use LB and RB helpers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
