# MCP Tool-Set Selection Specification

> Opt-in smaller tool-surface via SIMPLE_MCP_TOOL_SET env var or --tool-set= flag. Default is "auto" (core first, then upgrades to full 151 via list_changed). "core" serves a strict smaller subset via the T1 contract function _mcp_tools_list_json_for_set. "all" serves all 151 tools directly.

<!-- sdn-diagram:id=mcp_tool_set_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_tool_set_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_tool_set_spec -> std
mcp_tool_set_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_tool_set_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Tool-Set Selection Specification

Opt-in smaller tool-surface via SIMPLE_MCP_TOOL_SET env var or --tool-set= flag. Default is "auto" (core first, then upgrades to full 151 via list_changed). "core" serves a strict smaller subset via the T1 contract function _mcp_tools_list_json_for_set. "all" serves all 151 tools directly.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MCP-TOOLSET-001 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Active |
| Requirements | doc/03_plan/app/mcp/mcp_startup_perf_small_tasks_2026-06-12.md (task B4) |
| Source | `test/01_unit/app/mcp/mcp_tool_set_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Opt-in smaller tool-surface via SIMPLE_MCP_TOOL_SET env var or --tool-set= flag.
Default is "auto" (core first, then upgrades to full 151 via list_changed).
"core" serves a strict smaller subset via the T1 contract function
_mcp_tools_list_json_for_set. "all" serves all 151 tools directly.

## Dispatch constraint

tools/call dispatch is NOT filtered by the active tool set.
Clients holding a stale "all" list must still be able to call any tool
even when the server runs in "core" mode.  Only advertisement is filtered.

## T1 implementation note

_mcp_tools_list_json_for_set is implemented in main_static_tools.spl and filters
only tools/list advertisement. Dispatch remains unfiltered.

## Scenarios

### MCP tool-set — default (auto)

#### serves 151 tools in full list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = _mcp_static_tools_result()
val tool_count = count_occurrences(json, "{\"name\":")
expect(tool_count).to_equal(151)
```

</details>

#### full list contains play_wm_text_status

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = _mcp_static_tools_result()
expect(json.contains("\"play_wm_text_status\"")).to_equal(true)
```

</details>

#### full list contains simple_check

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = _mcp_static_tools_result()
expect(json.contains("\"simple_check\"")).to_equal(true)
```

</details>

#### full list starts with tools array wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = _mcp_static_tools_result()
expect(json.starts_with("{\"tools\":[")).to_equal(true)
```

</details>

### MCP tool-set — core mode

#### core result is a valid tools-array JSON object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val core_json = _mcp_tools_list_json_for_set("core")
expect(core_json.starts_with("{\"tools\":[")).to_equal(true)
expect(core_json.ends_with("]}")).to_equal(true)
```

</details>

#### core result contains at least one tool

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val core_json = _mcp_tools_list_json_for_set("core")
val core_count = count_occurrences(core_json, "{\"name\":")
expect(core_count).to_be_greater_than(0)
```

</details>

#### every tool in core result is also in full list

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val full_json = _mcp_static_tools_result()
val core_json = _mcp_tools_list_json_for_set("core")
val known_core_tool = "\"simple_read\""
val in_full = full_json.contains(known_core_tool)
val in_core = core_json.contains(known_core_tool)
expect(in_full).to_equal(true)
expect(in_core).to_equal(true)
```

</details>

#### core result has exactly 20 advertised tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val core_json = _mcp_tools_list_json_for_set("core")
expect(count_occurrences(core_json, "{\"name\":")).to_equal(20)
```

</details>

#### core result excludes non-core debug tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val core_json = _mcp_tools_list_json_for_set("core")
expect(core_json.contains("\"debug_create_session\"")).to_equal(false)
```

</details>

### MCP tool-set — dispatch is not filtered

#### simple_log is a registered tool (present in full advertised list)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# If dispatch filtered by tool set, simple_log would disappear from
# core-mode responses.  Asserting presence in the full list confirms
# the tool exists in the registry and dispatch can route it.
val json = _mcp_static_tools_result()
expect(json.contains("\"simple_log\"")).to_equal(true)
```

</details>

#### simple_squash is a registered tool (present in full advertised list)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = _mcp_static_tools_result()
expect(json.contains("\"simple_squash\"")).to_equal(true)
```

</details>

#### full list tool count is exactly 151 (dispatch table not shrunk)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A filtered dispatch table would reduce the count.
val json = _mcp_static_tools_result()
val count = count_occurrences(json, "{\"name\":")
expect(count).to_equal(151)
```

</details>

### MCP tool-set — argv selection plumbing

#### --tool-set=core switches the active set

-  mcp init tool set
   - Expected: _mcp_get_tool_set() equals `core`
-  mcp init tool set
   - Expected: _mcp_get_tool_set() equals `all`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["--tool-set=core"]
_mcp_init_tool_set(args)
expect(_mcp_get_tool_set()).to_equal("core")
val back = ["--tool-set=all"]
_mcp_init_tool_set(back)
expect(_mcp_get_tool_set()).to_equal("all")
```

</details>

#### --tool-set=auto switches the active set to auto

-  mcp init tool set
   - Expected: _mcp_get_tool_set() equals `auto`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["--tool-set=auto"]
_mcp_init_tool_set(args)
expect(_mcp_get_tool_set()).to_equal("auto")
```

</details>

#### invalid tool-set value falls back to auto (the default)

-  mcp init tool set
   - Expected: _mcp_get_tool_set() equals `auto`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["--tool-set=bogus"]
_mcp_init_tool_set(args)
expect(_mcp_get_tool_set()).to_equal("auto")
```

</details>

#### mcp_strip_tool_set_args removes only the flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = ["--tool-set=core", "--probe", "x"]
val stripped = mcp_strip_tool_set_args(args)
expect(stripped.len()).to_equal(2)
expect(stripped[0]).to_equal("--probe")
expect(stripped[1]).to_equal("x")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/03_plan/app/mcp/mcp_startup_perf_small_tasks_2026-06-12.md (task B4)](doc/03_plan/app/mcp/mcp_startup_perf_small_tasks_2026-06-12.md (task B4))


</details>
