# MCP Dynload Upgrade State Machine Specification

> When tool-set is "auto" the server advertises the 20-tool core list first, then upgrades to the full 151-tool list via a one-shot list_changed notification. This spec asserts the state machine in main.spl:

<!-- sdn-diagram:id=mcp_dynload_upgrade_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_dynload_upgrade_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_dynload_upgrade_spec -> std
mcp_dynload_upgrade_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_dynload_upgrade_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP Dynload Upgrade State Machine Specification

When tool-set is "auto" the server advertises the 20-tool core list first, then upgrades to the full 151-tool list via a one-shot list_changed notification. This spec asserts the state machine in main.spl:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #MCP-DYNLOAD-001 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | Active |
| Requirements | doc/03_plan/app/mcp/mcp_core_default_dynload_plan_2026-06-13.md |
| Source | `test/01_unit/app/mcp/mcp_dynload_upgrade_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

When tool-set is "auto" the server advertises the 20-tool core list first,
then upgrades to the full 151-tool list via a one-shot list_changed
notification. This spec asserts the state machine in main.spl:

  _mcp_tools_list_payload() — returns core (20 tools) on first call in auto
                               mode; returns full (151 tools) on all later calls
  _mcp_list_upgraded()      — false before first payload; true after
  _mcp_take_emit_list_changed() — one-shot: true once (after first auto serve),
                               then false forever

## State-ordering note

Module-level vars (_MCP_LIST_UPGRADED, one-shot flag) persist across `it`
blocks in a single file. Each `it` block calls _mcp_init_tool_set first to
reset the tool-set selection; however _MCP_LIST_UPGRADED may not reset on
re-init (impl detail). Tests are ordered so the auto-mode block runs first and
subsequent blocks explicitly re-init before asserting their invariants.

## Payload count method

Tool count = split("{\"name\":").len() - 1  (same approach as existing specs)

## Scenarios

### MCP dynload upgrade — auto mode (run first)

#### auto mode: pre-payload upgraded flag is false

-  mcp init tool set
   - Expected: _mcp_get_tool_set() equals `auto`
   - Expected: _mcp_list_upgraded() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reset = ["--tool-set=auto"]
_mcp_init_tool_set(reset)
expect(_mcp_get_tool_set()).to_equal("auto")
# NOTE: If impl resets _MCP_LIST_UPGRADED on _mcp_init_tool_set,
# this is a clean start. If not, a prior test run may have flipped it.
# The contract says default state is false; we assert it here.
expect(_mcp_list_upgraded()).to_equal(false)
```

</details>

#### auto mode: first payload has exactly 20 tools

-  mcp init tool set
   - Expected: count equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reset = ["--tool-set=auto"]
_mcp_init_tool_set(reset)
val payload = _mcp_tools_list_payload()
val count = count_tools_in_payload(payload)
expect(count).to_equal(20)
```

</details>

#### auto mode: first payload starts with tools array wrapper

-  mcp init tool set
   - Expected: payload.starts_with("{\"tools\":[") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reset = ["--tool-set=auto"]
_mcp_init_tool_set(reset)
val payload = _mcp_tools_list_payload()
expect(payload.starts_with("{\"tools\":[")).to_equal(true)
```

</details>

#### auto mode: upgraded flag is true after first payload

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Depends on the first-payload `it` having run above (state persists).
expect(_mcp_list_upgraded()).to_equal(true)
```

</details>

#### auto mode: take_emit_list_changed is true once then false

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# First call: should be true (one-shot, consumed by first auto serve)
val first = _mcp_take_emit_list_changed()
expect(first).to_equal(true)
# Second call immediately: must be false (one-shot consumed)
val second = _mcp_take_emit_list_changed()
expect(second).to_equal(false)
```

</details>

#### auto mode: second payload has exactly 151 tools

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After upgrade flag is set, all subsequent payloads serve full list.
val payload = _mcp_tools_list_payload()
val count = count_tools_in_payload(payload)
expect(count).to_equal(151)
```

</details>

#### auto mode: second payload starts with tools array wrapper

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val payload = _mcp_tools_list_payload()
expect(payload.starts_with("{\"tools\":[")).to_equal(true)
```

</details>

### MCP dynload upgrade — all mode

#### all mode: first payload has exactly 151 tools

-  mcp init tool set
   - Expected: _mcp_get_tool_set() equals `all`
   - Expected: count equals `151`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reset = ["--tool-set=all"]
_mcp_init_tool_set(reset)
expect(_mcp_get_tool_set()).to_equal("all")
val payload = _mcp_tools_list_payload()
val count = count_tools_in_payload(payload)
expect(count).to_equal(151)
```

</details>

#### all mode: payload starts with tools array wrapper

-  mcp init tool set
   - Expected: payload.starts_with("{\"tools\":[") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reset = ["--tool-set=all"]
_mcp_init_tool_set(reset)
val payload = _mcp_tools_list_payload()
expect(payload.starts_with("{\"tools\":[")).to_equal(true)
```

</details>

#### all mode: take_emit_list_changed is false (no upgrade notification)

-  mcp init tool set
   - Expected: changed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reset = ["--tool-set=all"]
_mcp_init_tool_set(reset)
val changed = _mcp_take_emit_list_changed()
expect(changed).to_equal(false)
```

</details>

### MCP dynload upgrade — core mode

#### core mode: first payload has exactly 20 tools

-  mcp init tool set
   - Expected: _mcp_get_tool_set() equals `core`
   - Expected: count equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reset = ["--tool-set=core"]
_mcp_init_tool_set(reset)
expect(_mcp_get_tool_set()).to_equal("core")
val payload = _mcp_tools_list_payload()
val count = count_tools_in_payload(payload)
expect(count).to_equal(20)
```

</details>

#### core mode: payload starts with tools array wrapper

-  mcp init tool set
   - Expected: payload.starts_with("{\"tools\":[") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reset = ["--tool-set=core"]
_mcp_init_tool_set(reset)
val payload = _mcp_tools_list_payload()
expect(payload.starts_with("{\"tools\":[")).to_equal(true)
```

</details>

#### core mode: second payload still has exactly 20 tools (no upgrade)

-  mcp init tool set
   - Expected: count equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reset = ["--tool-set=core"]
_mcp_init_tool_set(reset)
val _ = _mcp_tools_list_payload()
val second = _mcp_tools_list_payload()
val count = count_tools_in_payload(second)
expect(count).to_equal(20)
```

</details>

#### core mode: take_emit_list_changed is false

-  mcp init tool set
   - Expected: changed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reset = ["--tool-set=core"]
_mcp_init_tool_set(reset)
val changed = _mcp_take_emit_list_changed()
expect(changed).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/03_plan/app/mcp/mcp_core_default_dynload_plan_2026-06-13.md](doc/03_plan/app/mcp/mcp_core_default_dynload_plan_2026-06-13.md)


</details>
