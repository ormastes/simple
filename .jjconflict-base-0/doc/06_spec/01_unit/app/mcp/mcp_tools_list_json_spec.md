# MCP tools/list JSON Well-Formedness Specification

> Regression guard for the MCP `tools/list` serializer. A stale/regressed serializer once emitted tool objects that were missing their closing brace (`...,"annotations":{...},{"name":...`), producing invalid JSON and a `tools_count=0` smoke failure even though the server "responded".

<!-- sdn-diagram:id=mcp_tools_list_json_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_tools_list_json_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_tools_list_json_spec -> std
mcp_tools_list_json_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_tools_list_json_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = _mcp_static_tools_result()
expect(json.starts_with("{\"tools\":[")).to_equal(true)
expect(json.ends_with("]}")).to_equal(true)
```

</details>

#### closes every tool object before the next one starts

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = _mcp_static_tools_result()
val tool_count = count_occurrences(json, "{\"name\":")
expect(tool_count > 100).to_equal(true)
```

</details>

#### includes core diagnostics and vcs tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = _mcp_static_tools_result()
expect(json.contains("\"simple_check\"")).to_equal(true)
expect(json.contains("\"simple_run\"")).to_equal(true)
expect(json.contains("\"simple_commit\"")).to_equal(true)
```

</details>

#### includes the play_wm_text_* window-text-access tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
