# MCP Static Tools — Perf-Rewrite Correctness Oracle

> Correctness guard for the Team T1 quadratic-concat elimination rewrite of main_static_tools.spl. The rewrite replaces O(n^2) `acc = acc + piece` patterns with parts-array + `.join(",")` calls throughout:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 27 | 27 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Static Tools — Perf-Rewrite Correctness Oracle

Correctness guard for the Team T1 quadratic-concat elimination rewrite of main_static_tools.spl. The rewrite replaces O(n^2) `acc = acc + piece` patterns with parts-array + `.join(",")` calls throughout:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MCP-PERF-T1-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Active |
| Requirements | doc/03_plan/app/mcp/mcp_startup_perf_small_tasks_2026-06-12.md (task B2, T1) |
| Source | `test/01_unit/app/mcp/mcp_static_tools_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Correctness guard for the Team T1 quadratic-concat elimination rewrite of
main_static_tools.spl. The rewrite replaces O(n^2) `acc = acc + piece` patterns
with parts-array + `.join(",")` calls throughout:

- `_mcp_static_props`: 36 sequential appends -> parts array + join
- `_mcp_static_tools_result`: 151-tool loop body -> schemas array + join
- `_mcp_hex_u64`: nibble concat loop -> parts array + join
- `--probe`: cheap native startup check; manifest content is verified by tools/list specs

## Correctness contract

The rewrite must produce byte-identical output to the pre-rewrite baseline:
- Exactly 38114 characters (JSON string length, newline not included)
- Exactly 151 tool objects (same as baseline)
- play_wm_text_status, first tool (debug_create_session), last tool (debug_ui_css_dump) present
- Balanced braces and brackets

## Core subset

`_mcp_tools_list_json_for_set("core")` must return a strict subset of the full
list containing the 20 core dev tools and nothing else.
`_mcp_tools_list_json_for_set("all")` must be byte-identical to
`_mcp_static_tools_result()`.

## Scenarios

### T1 rewrite — byte-identical output oracle

#### json string length is 38114 characters

- json string length is 38114 characters
   - Expected: result.len() equals `38114`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("json string length is 38114 characters")
val result = _mcp_static_tools_result()
expect(result.len()).to_equal(38114)
```

</details>

#### has exactly 151 tool objects

- has exactly 151 tool objects
   - Expected: tool_count equals `151`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("has exactly 151 tool objects")
val result = _mcp_static_tools_result()
val tool_count = count_substr(result, "{\"name\":")
expect(tool_count).to_equal(151)
```

</details>

#### is wrapped as tools array object

- is wrapped as tools array object
   - Expected: result.starts_with("{\"tools\":[") is true
   - Expected: result.ends_with("]}") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("is wrapped as tools array object")
val result = _mcp_static_tools_result()
expect(result.starts_with("{\"tools\":[")).to_equal(true)
expect(result.ends_with("]}")).to_equal(true)
```

</details>

#### first tool is debug_create_session

- first tool is debug_create_session
   - Expected: result.starts_with(expected_start) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("first tool is debug_create_session")
val result = _mcp_static_tools_result()
val expected_start = "{\"tools\":[{\"name\":\"debug_create_session\""
expect(result.starts_with(expected_start)).to_equal(true)
```

</details>

#### last tool is debug_ui_css_dump

- last tool is debug_ui_css_dump
   - Expected: result contains `"debug_ui_css_dump"`
   - Expected: after_marker.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("last tool is debug_ui_css_dump")
val result = _mcp_static_tools_result()
expect(result.contains("\"debug_ui_css_dump\"")).to_equal(true)
val last_name_marker = "\"name\":\"debug_ui_css_dump\""
val after_marker = result.split(last_name_marker)
expect(after_marker.len()).to_equal(2)
```

</details>

#### play_wm_text_status is present

- play_wm_text_status is present
   - Expected: result contains `"play_wm_text_status"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("play_wm_text_status is present")
val result = _mcp_static_tools_result()
expect(result.contains("\"play_wm_text_status\"")).to_equal(true)
```

</details>

#### tool boundary pattern is well-formed (no missing closing braces)

- tool boundary pattern is well-formed (no missing closing braces)
   - Expected: closed_boundaries equals `tool_starts - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("tool boundary pattern is well-formed (no missing closing braces)")
val result = _mcp_static_tools_result()
val tool_starts = count_substr(result, "{\"name\":")
val closed_boundaries = count_substr(result, "}},{\"name\":")
expect(closed_boundaries).to_equal(tool_starts - 1)
```

</details>

#### braces are balanced

- braces are balanced
   - Expected: count_substr(result, "{") equals `count_substr(result, "}")`
   - Expected: count_substr(result, "[") equals `count_substr(result, "]")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("braces are balanced")
val result = _mcp_static_tools_result()
expect(count_substr(result, "{")).to_equal(count_substr(result, "}"))
expect(count_substr(result, "[")).to_equal(count_substr(result, "]"))
```

</details>

### T1 rewrite — _mcp_tools_list_json_for_set

#### set=all is byte-identical to _mcp_static_tools_result

- set=all is byte-identical to _mcp_static_tools_result
   - Expected: full_via_set.len() equals `full_direct.len()`
   - Expected: full_via_set equals `full_direct`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("set=all is byte-identical to _mcp_static_tools_result")
val full_direct = _mcp_static_tools_result()
val full_via_set = _mcp_tools_list_json_for_set("all")
expect(full_via_set.len()).to_equal(full_direct.len())
expect(full_via_set).to_equal(full_direct)
```

</details>

#### set=all has exactly 151 tools

- set=all has exactly 151 tools
   - Expected: count_substr(result, "{\"name\":") equals `151`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("set=all has exactly 151 tools")
val result = _mcp_tools_list_json_for_set("all")
expect(count_substr(result, "{\"name\":")).to_equal(151)
```

</details>

#### set=core is valid tools-array JSON

- set=core is valid tools-array JSON
   - Expected: result.starts_with("{\"tools\":[") is true
   - Expected: result.ends_with("]}") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("set=core is valid tools-array JSON")
val result = _mcp_tools_list_json_for_set("core")
expect(result.starts_with("{\"tools\":[")).to_equal(true)
expect(result.ends_with("]}")).to_equal(true)
```

</details>

#### set=core has fewer tools than set=all

- set=core has fewer tools than set=all
   - Expected: core_count < all_count is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("set=core has fewer tools than set=all")
val core_count = count_substr(_mcp_tools_list_json_for_set("core"), "{\"name\":")
val all_count = count_substr(_mcp_tools_list_json_for_set("all"), "{\"name\":")
expect(core_count < all_count).to_equal(true)
```

</details>

#### set=core contains simple_check

- set=core contains simple_check
   - Expected: result contains `"simple_check"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("set=core contains simple_check")
val result = _mcp_tools_list_json_for_set("core")
expect(result.contains("\"simple_check\"")).to_equal(true)
```

</details>

#### set=core contains simple_read

- set=core contains simple_read
   - Expected: result contains `"simple_read"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("set=core contains simple_read")
val result = _mcp_tools_list_json_for_set("core")
expect(result.contains("\"simple_read\"")).to_equal(true)
```

</details>

#### set=core contains simple_edit

- set=core contains simple_edit
   - Expected: result contains `"simple_edit"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("set=core contains simple_edit")
val result = _mcp_tools_list_json_for_set("core")
expect(result.contains("\"simple_edit\"")).to_equal(true)
```

</details>

#### set=core contains simple_run

- set=core contains simple_run
   - Expected: result contains `"simple_run"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("set=core contains simple_run")
val result = _mcp_tools_list_json_for_set("core")
expect(result.contains("\"simple_run\"")).to_equal(true)
```

</details>

#### set=core contains simple_test

- set=core contains simple_test
   - Expected: result contains `"simple_test"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("set=core contains simple_test")
val result = _mcp_tools_list_json_for_set("core")
expect(result.contains("\"simple_test\"")).to_equal(true)
```

</details>

#### set=core contains simple_commit

- set=core contains simple_commit
   - Expected: result contains `"simple_commit"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("set=core contains simple_commit")
val result = _mcp_tools_list_json_for_set("core")
expect(result.contains("\"simple_commit\"")).to_equal(true)
```

</details>

#### set=core does NOT contain debug-only tools

- set=core does NOT contain debug-only tools
   - Expected: result does not contain `"debug_create_session"`
   - Expected: result does not contain `"debug_set_breakpoint"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("set=core does NOT contain debug-only tools")
val result = _mcp_tools_list_json_for_set("core")
expect(result.contains("\"debug_create_session\"")).to_equal(false)
expect(result.contains("\"debug_set_breakpoint\"")).to_equal(false)
```

</details>

#### set=core does NOT contain play_ tools

- set=core does NOT contain play_ tools
   - Expected: result does not contain `"play_run"`
   - Expected: result does not contain `"play_wm_text_status"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("set=core does NOT contain play_ tools")
val result = _mcp_tools_list_json_for_set("core")
expect(result.contains("\"play_run\"")).to_equal(false)
expect(result.contains("\"play_wm_text_status\"")).to_equal(false)
```

</details>

#### set=core has exactly 20 tools

- set=core has exactly 20 tools
   - Expected: core_count equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("set=core has exactly 20 tools")
val result = _mcp_tools_list_json_for_set("core")
val core_count = count_substr(result, "{\"name\":")
expect(core_count).to_equal(20)
```

</details>

#### unknown set name falls back to full list

- unknown set name falls back to full list
   - Expected: count_substr(result, "{\"name\":") equals `151`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("unknown set name falls back to full list")
val result = _mcp_tools_list_json_for_set("unknown_set")
expect(count_substr(result, "{\"name\":")).to_equal(151)
```

</details>

### full-list cache

#### first call returns exact length 38114

- first call returns exact length 38114
   - Expected: result.len() equals `38114`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("first call returns exact length 38114")
val result = _mcp_static_tools_result_cached()
expect(result.len()).to_equal(38114)
```

</details>

#### first call has exactly 151 occurrences of {\

- first call has exactly 151 occurrences of {\
   - Expected: tool_count equals `151`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("first call has exactly 151 occurrences of {\")
val result = _mcp_static_tools_result_cached()
val tool_count = count_substr(result, "{\"name\":")
expect(tool_count).to_equal(151)
```

</details>

#### second call returns exact length 38114 (cached path correctness)

- second call returns exact length 38114 (cached path correctness)
   - Expected: second.len() equals `38114`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("second call returns exact length 38114 (cached path correctness)")
val first = _mcp_static_tools_result_cached()
val second = _mcp_static_tools_result_cached()
expect(second.len()).to_equal(38114)
```

</details>

#### second call equals first call (cache returns same content)

- second call equals first call (cache returns same content)
   - Expected: second equals `first`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("second call equals first call (cache returns same content)")
val first = _mcp_static_tools_result_cached()
val second = _mcp_static_tools_result_cached()
expect(second).to_equal(first)
```

</details>

#### cached result equals independent _mcp_static_tools_result() output

- cached result equals independent _mcp_static_tools_result() output
   - Expected: cached equals `direct`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("cached result equals independent _mcp_static_tools_result() output")
val cached = _mcp_static_tools_result_cached()
val direct = _mcp_static_tools_result()
expect(cached).to_equal(direct)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 27 |
| Active scenarios | 27 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/03_plan/app/mcp/mcp_startup_perf_small_tasks_2026-06-12.md (task B2, T1)`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-MCP-PERF-T1-001`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `525374a85cdbf01ab1db1ac284f5c8407d82343d70e2fc451d89be2662a18344`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `525374a85cdbf01ab1db1ac284f5c8407d82343d70e2fc451d89be2662a18344`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `525374a85cdbf01ab1db1ac284f5c8407d82343d70e2fc451d89be2662a18344`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/mcp/mcp_static_tools_perf_spec.spl
mirror: doc/06_spec/01_unit/app/mcp/mcp_static_tools_perf_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/app/mcp/mcp_static_tools_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/mcp/mcp_static_tools_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/mcp/mcp_static_tools_perf_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/mcp/mcp_static_tools_perf_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/mcp/mcp_static_tools_perf_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'json string length is 38114 characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/mcp/mcp_static_tools_perf_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has exactly 151 tool objects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/mcp/mcp_static_tools_perf_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is wrapped as tools array object' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
