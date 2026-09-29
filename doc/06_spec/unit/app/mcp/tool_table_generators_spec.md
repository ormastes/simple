# Tool Table Generators Specification

> Tests covering simple_feature_gen tool entry, simple_task_gen tool entry, simple_todo_gen tool entry, simple_spec_gen tool entry, simple_spec_coverage tool entry.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tool Table Generators Specification

## Scenarios

### simple_feature_gen tool entry

#### has no name parameter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has no name parameter
   - Expected: has_name is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has no name parameter")
val entry = _find_tool_entry("simple_feature_gen")
val has_name = entry.props.contains_key("name")
expect(has_name).to_equal(false)
```

</details>

#### has a non-empty description

- has a non-empty description
   - Expected: entry.description.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has a non-empty description")
val entry = _find_tool_entry("simple_feature_gen")
expect(entry.description.len() > 0).to_equal(true)
```

</details>

#### description mentions feature or regenerate

- description mentions feature or regenerate
   - Expected: mentions_feature is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("description mentions feature or regenerate")
val entry = _find_tool_entry("simple_feature_gen")
val desc_lower = entry.description.lower()
val mentions_feature = desc_lower.contains("feature") or desc_lower.contains("regenerate")
expect(mentions_feature).to_equal(true)
```

</details>

### simple_task_gen tool entry

#### has no name parameter

- has no name parameter
   - Expected: has_name is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has no name parameter")
val entry = _find_tool_entry("simple_task_gen")
val has_name = entry.props.contains_key("name")
expect(has_name).to_equal(false)
```

</details>

#### has a non-empty description

- has a non-empty description
   - Expected: entry.description.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has a non-empty description")
val entry = _find_tool_entry("simple_task_gen")
expect(entry.description.len() > 0).to_equal(true)
```

</details>

### simple_todo_gen tool entry

#### has read_only set to true

- has read_only set to true
   - Expected: entry.read_only is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has read_only set to true")
val entry = _find_tool_entry("simple_todo_gen")
expect(entry.read_only).to_equal(true)
```

</details>

### simple_spec_gen tool entry

#### has path parameter

- has path parameter
   - Expected: has_path is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has path parameter")
val entry = _find_tool_entry("simple_spec_gen")
val has_path = entry.props.contains_key("path")
expect(has_path).to_equal(true)
```

</details>

### simple_spec_coverage tool entry

#### has read_only set to true

- has read_only set to true
   - Expected: entry.read_only is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has read_only set to true")
val entry = _find_tool_entry("simple_spec_coverage")
expect(entry.read_only).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp/tool_table_generators_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering simple_feature_gen tool entry, simple_task_gen tool entry, simple_todo_gen tool entry, simple_spec_gen tool entry, simple_spec_coverage tool entry.
- simple_feature_gen tool entry
- simple_task_gen tool entry
- simple_todo_gen tool entry
- simple_spec_gen tool entry
- simple_spec_coverage tool entry

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
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

- Canonical SPipe generation for source `f60d48102f79afe0d2451a9d83d889b3e463f5c49042b1ce9649237e5c665f96`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f60d48102f79afe0d2451a9d83d889b3e463f5c49042b1ce9649237e5c665f96`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f60d48102f79afe0d2451a9d83d889b3e463f5c49042b1ce9649237e5c665f96`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/mcp/tool_table_generators_spec.spl
mirror: doc/06_spec/unit/app/mcp/tool_table_generators_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp/tool_table_generators_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp/tool_table_generators_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp/tool_table_generators_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has no name parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp/tool_table_generators_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has a non-empty description' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp/tool_table_generators_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'description mentions feature or regenerate' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
