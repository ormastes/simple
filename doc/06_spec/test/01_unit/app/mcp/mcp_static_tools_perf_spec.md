# MCP Static Tools — Perf-Rewrite Correctness Oracle

> Correctness guard for the Team T1 quadratic-concat elimination rewrite of main_static_tools.spl. The rewrite replaces O(n^2) `acc = acc + piece` patterns with parts-array + `.join(",")` calls throughout:

<!-- sdn-diagram:id=mcp_static_tools_perf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_static_tools_perf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_static_tools_perf_spec -> std
mcp_static_tools_perf_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_static_tools_perf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_static_tools_result()
expect(result.len()).to_equal(38114)
```

</details>

#### has exactly 151 tool objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_static_tools_result()
val tool_count = count_substr(result, "{\"name\":")
expect(tool_count).to_equal(151)
```

</details>

#### is wrapped as tools array object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_static_tools_result()
expect(result.starts_with("{\"tools\":[")).to_equal(true)
expect(result.ends_with("]}")).to_equal(true)
```

</details>

#### first tool is debug_create_session

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_static_tools_result()
val expected_start = "{\"tools\":[{\"name\":\"debug_create_session\""
expect(result.starts_with(expected_start)).to_equal(true)
```

</details>

#### last tool is debug_ui_css_dump

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_static_tools_result()
expect(result.contains("\"debug_ui_css_dump\"")).to_equal(true)
val last_name_marker = "\"name\":\"debug_ui_css_dump\""
val after_marker = result.split(last_name_marker)
expect(after_marker.len()).to_equal(2)
```

</details>

#### play_wm_text_status is present

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_static_tools_result()
expect(result.contains("\"play_wm_text_status\"")).to_equal(true)
```

</details>

#### tool boundary pattern is well-formed (no missing closing braces)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_static_tools_result()
val tool_starts = count_substr(result, "{\"name\":")
val closed_boundaries = count_substr(result, "}},{\"name\":")
expect(closed_boundaries).to_equal(tool_starts - 1)
```

</details>

#### braces are balanced

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_static_tools_result()
expect(count_substr(result, "{")).to_equal(count_substr(result, "}"))
expect(count_substr(result, "[")).to_equal(count_substr(result, "]"))
```

</details>

### T1 rewrite — _mcp_tools_list_json_for_set

#### set=all is byte-identical to _mcp_static_tools_result

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_direct = _mcp_static_tools_result()
val full_via_set = _mcp_tools_list_json_for_set("all")
expect(full_via_set.len()).to_equal(full_direct.len())
expect(full_via_set).to_equal(full_direct)
```

</details>

#### set=all has exactly 151 tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_tools_list_json_for_set("all")
expect(count_substr(result, "{\"name\":")).to_equal(151)
```

</details>

#### set=core is valid tools-array JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_tools_list_json_for_set("core")
expect(result.starts_with("{\"tools\":[")).to_equal(true)
expect(result.ends_with("]}")).to_equal(true)
```

</details>

#### set=core has fewer tools than set=all

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val core_count = count_substr(_mcp_tools_list_json_for_set("core"), "{\"name\":")
val all_count = count_substr(_mcp_tools_list_json_for_set("all"), "{\"name\":")
expect(core_count < all_count).to_equal(true)
```

</details>

#### set=core contains simple_check

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_tools_list_json_for_set("core")
expect(result.contains("\"simple_check\"")).to_equal(true)
```

</details>

#### set=core contains simple_read

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_tools_list_json_for_set("core")
expect(result.contains("\"simple_read\"")).to_equal(true)
```

</details>

#### set=core contains simple_edit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_tools_list_json_for_set("core")
expect(result.contains("\"simple_edit\"")).to_equal(true)
```

</details>

#### set=core contains simple_run

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_tools_list_json_for_set("core")
expect(result.contains("\"simple_run\"")).to_equal(true)
```

</details>

#### set=core contains simple_test

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_tools_list_json_for_set("core")
expect(result.contains("\"simple_test\"")).to_equal(true)
```

</details>

#### set=core contains simple_commit

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_tools_list_json_for_set("core")
expect(result.contains("\"simple_commit\"")).to_equal(true)
```

</details>

#### set=core does NOT contain debug-only tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_tools_list_json_for_set("core")
expect(result.contains("\"debug_create_session\"")).to_equal(false)
expect(result.contains("\"debug_set_breakpoint\"")).to_equal(false)
```

</details>

#### set=core does NOT contain play_ tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_tools_list_json_for_set("core")
expect(result.contains("\"play_run\"")).to_equal(false)
expect(result.contains("\"play_wm_text_status\"")).to_equal(false)
```

</details>

#### set=core has exactly 20 tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_tools_list_json_for_set("core")
val core_count = count_substr(result, "{\"name\":")
expect(core_count).to_equal(20)
```

</details>

#### unknown set name falls back to full list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = _mcp_tools_list_json_for_set("unknown_set")
expect(count_substr(result, "{\"name\":")).to_equal(151)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/03_plan/app/mcp/mcp_startup_perf_small_tasks_2026-06-12.md (task B2, T1)](doc/03_plan/app/mcp/mcp_startup_perf_small_tasks_2026-06-12.md (task B2, T1))


</details>
