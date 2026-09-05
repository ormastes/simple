# Symbol Table Specification

> Tests covering extract_json_string for symbol data.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Symbol Table Specification

## Scenarios

### extract_json_string for symbol data

#### extracts symbol name from JSON

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts symbol name from JSON
   - Expected: extract_json_string(json, "name") equals `MyClass`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts symbol name from JSON")
val json = jo2(jp("name", js("MyClass")), jp("kind", js("class")))
expect(extract_json_string(json, "name")).to_equal("MyClass")
```

</details>

#### extracts symbol kind

- extracts symbol kind
   - Expected: extract_json_string(json, "kind") equals `function`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts symbol kind")
val json = jo2(jp("name", js("helper")), jp("kind", js("function")))
expect(extract_json_string(json, "kind")).to_equal("function")
```

</details>

#### extracts module path

- extracts module path
   - Expected: extract_json_string(json, "module") equals `mcp.simple_lang`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts module path")
val json = jo1(jp("module", js("mcp.simple_lang")))
expect(extract_json_string(json, "module")).to_equal("mcp.simple_lang")
```

</details>

#### returns empty for missing symbol

- returns empty for missing symbol
   - Expected: extract_json_string(json, "kind") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty for missing symbol")
val json = jo1(jp("name", js("test")))
expect(extract_json_string(json, "kind")).to_equal("")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/symbol_table_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering extract_json_string for symbol data.
- extract_json_string for symbol data

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7c3c451b1944b978bb3d3230de17009ce94ff58c77c691d7f34e12ed014f5754`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7c3c451b1944b978bb3d3230de17009ce94ff58c77c691d7f34e12ed014f5754`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7c3c451b1944b978bb3d3230de17009ce94ff58c77c691d7f34e12ed014f5754`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp_unit/symbol_table_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/symbol_table_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/symbol_table_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/symbol_table_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/symbol_table_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts symbol name from JSON' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/symbol_table_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts symbol kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/symbol_table_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts module path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
