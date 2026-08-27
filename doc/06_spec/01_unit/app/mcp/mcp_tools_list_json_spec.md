# MCP tools/list JSON Well-Formedness Specification

> Regression guard for the MCP `tools/list` serializer. A stale/regressed serializer once emitted tool objects that were missing their closing brace (`...,"annotations":{...},{"name":...`), producing invalid JSON and a `tools_count=0` smoke failure even though the server "responded".

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP tools/list JSON Well-Formedness Specification

Regression guard for the MCP `tools/list` serializer. A stale/regressed serializer once emitted tool objects that were missing their closing brace (`...,"annotations":{...},{"name":...`), producing invalid JSON and a `tools_count=0` smoke failure even though the server "responded".

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MCP-JSON-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Active |
| Requirements | N/A |
| Source | `test/01_unit/app/mcp/mcp_tools_list_json_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Regression guard for the MCP `tools/list` serializer. A stale/regressed
serializer once emitted tool objects that were missing their closing brace
(`...,"annotations":{...},{"name":...`), producing invalid JSON and a
`tools_count=0` smoke failure even though the server "responded".

These tests call the in-process tool-list builder directly through the
interpreter (no native build required), so the serializer is guarded on
every test run regardless of which deploy lane built the shipped binary.

## Behavior

- `_mcp_static_tools_result()` returns a single balanced JSON object.
- Every `{`/`[` is matched; the running nesting depth never goes negative
  and ends at zero (this is what catches a tool object missing its `}`).
- The payload is shaped as `{"tools":[ ... ]}` with one object per tool.
- The advertised tool set still includes the core and `play_wm_text_*`
  tools, so a silently-truncated list is caught too.

## Scenarios

### MCP tools/list serializer — JSON well-formedness

#### is shaped as a tools array object

- is shaped as a tools array object
   - Expected: json.starts_with("{\"tools\":[") is true
   - Expected: json.ends_with("]}") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is shaped as a tools array object")
val json = _mcp_static_tools_result()
expect(json.starts_with("{\"tools\":[")).to_equal(true)
expect(json.ends_with("]}")).to_equal(true)
```

</details>

#### closes every tool object before the next one starts

- closes every tool object before the next one starts
   - Expected: closed_boundaries equals `tool_starts - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("closes every tool object before the next one starts")
# The original bug emitted the tool boundary as `},{"name"` — the
# tool object's closing brace was dropped. A well-formed boundary is
# `}},{"name"`: annotations object close, tool object close, comma,
# next tool. There are exactly (N - 1) boundaries between N tools.
val json = _mcp_static_tools_result()
val tool_starts = count_occurrences(json, "{\"name\":")
val closed_boundaries = count_occurrences(json, "}},{\"name\":")
expect(closed_boundaries).to_equal(tool_starts - 1)
```

</details>

#### has balanced top-level brace and bracket counts

- has balanced top-level brace and bracket counts
   - Expected: count_occurrences(json, "{") equals `count_occurrences(json, "}")`
   - Expected: count_occurrences(json, "[") equals `count_occurrences(json, "]")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("has balanced top-level brace and bracket counts")
# Cheap whole-payload sanity check: a dropped tool-object brace makes
# '{' outnumber '}'. (Counts are equal because every JSON string in
# the payload that contains a brace is itself balanced.)
val json = _mcp_static_tools_result()
expect(count_occurrences(json, "{")).to_equal(count_occurrences(json, "}"))
expect(count_occurrences(json, "[")).to_equal(count_occurrences(json, "]"))
```

</details>

### MCP tools/list serializer — advertised tools

#### advertises a substantial tool set

- advertises a substantial tool set
   - Expected: tool_count > 100 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("advertises a substantial tool set")
val json = _mcp_static_tools_result()
val tool_count = count_occurrences(json, "{\"name\":")
expect(tool_count > 100).to_equal(true)
```

</details>

#### includes core diagnostics and vcs tools

- includes core diagnostics and vcs tools
   - Expected: json contains `"simple_check"`
   - Expected: json contains `"simple_run"`
   - Expected: json contains `"simple_commit"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("includes core diagnostics and vcs tools")
val json = _mcp_static_tools_result()
expect(json.contains("\"simple_check\"")).to_equal(true)
expect(json.contains("\"simple_run\"")).to_equal(true)
expect(json.contains("\"simple_commit\"")).to_equal(true)
```

</details>

#### includes the play_wm_text_* window-text-access tools

- includes the play_wm_text_* window-text-access tools
   - Expected: json contains `"play_wm_text_status"`
   - Expected: json contains `"play_wm_text_snapshot"`
   - Expected: json contains `"play_wm_text_find"`
   - Expected: json contains `"play_wm_text_act"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("includes the play_wm_text_* window-text-access tools")
val json = _mcp_static_tools_result()
expect(json.contains("\"play_wm_text_status\"")).to_equal(true)
expect(json.contains("\"play_wm_text_snapshot\"")).to_equal(true)
expect(json.contains("\"play_wm_text_find\"")).to_equal(true)
expect(json.contains("\"play_wm_text_act\"")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-MCP-JSON-001`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d7048b142e72d5370b0930aa0da247146cbe459821af759c5710a641c0288412`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d7048b142e72d5370b0930aa0da247146cbe459821af759c5710a641c0288412`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d7048b142e72d5370b0930aa0da247146cbe459821af759c5710a641c0288412`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/mcp/mcp_tools_list_json_spec.spl
mirror: doc/06_spec/01_unit/app/mcp/mcp_tools_list_json_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/app/mcp/mcp_tools_list_json_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/mcp/mcp_tools_list_json_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/mcp/mcp_tools_list_json_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/mcp/mcp_tools_list_json_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is shaped as a tools array object' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/mcp/mcp_tools_list_json_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'closes every tool object before the next one starts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/mcp/mcp_tools_list_json_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has balanced top-level brace and bracket counts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
