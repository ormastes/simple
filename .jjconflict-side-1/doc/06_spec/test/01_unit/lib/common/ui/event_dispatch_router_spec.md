# Event Dispatch Router Spec

> `process_event` is the single entry point that turns a `UIEvent` into a new `UIState`. This spec covers two parts of that dispatch that had no direct branch coverage:

<!-- sdn-diagram:id=event_dispatch_router_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=event_dispatch_router_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

event_dispatch_router_spec -> std
event_dispatch_router_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=event_dispatch_router_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Event Dispatch Router Spec

`process_event` is the single entry point that turns a `UIEvent` into a new `UIState`. This spec covers two parts of that dispatch that had no direct branch coverage:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/common/ui/event_dispatch_router_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`process_event` is the single entry point that turns a `UIEvent` into a new
`UIState`. This spec covers two parts of that dispatch that had no direct
branch coverage:

- **`handle_action`** is a string-prefix router (`focus_`, `tab_`, `toggle_`,
  `sort_col_`, `filter_`, `select_`) reached via `UIEvent.Action(name)`. Each
  prefix is exercised once, including the unknown-prefix fallthrough that
  returns the state unchanged.
- **`process_event` -> `handle_pointer`** is exercised through the public
  `(state, event) -> state` reducer signature directly (a `TouchPress`
  routed to a button moves `focused_id`), not through the private
  `widget_hit.spl` internals a different spec already targets.

## GPU lane scheduler

A second describe block (in the same file, since both are dispatch/router
branch coverage for the CPU event path) drives every individual reject guard
in `engine2d_host_gpu_lane_schedule` (`backend_lane.spl`) with the minimal
input that trips each one, plus one accepting call to show the guards are
the exception rather than the rule. `estimated_ms` is asserted equal to
`baseline_ms` on the accepting call: the earlier `baseline_ms/2` fabricated
"GPU speedup" telemetry noted in research has been removed from this
function; `estimated_ms` is a plain passthrough today, and this spec pins
that down so no fabricated multiplier can quietly return.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** N/A

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Examples

The "focus_<id> moves focus to an existing widget" scenario routes
`UIEvent.Action("focus_<id>")` through `handle_action` and asserts the
returned state's `focused_id` field, then repeats with a missing id to show
the no-op fallback. The GPU-lane block drives each `engine2d_host_gpu_lane_schedule`
reject guard (invalid lane, oversized packet, host-semantic mutation,
per-widget dispatch, non-coarse batch) with the minimal input that trips it.

## Scenarios

### handle_action — string-prefix router

#### focus_<id> moves focus to an existing widget, and is a no-op for a missing one

- Route focus_<target> to an id that exists in the tree
   - Expected: found.focused_id equals `focus_target`
- Route focus_<missing> to an id that is not in the tree
   - Expected: missing.focused_id equals `state.focused_id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Route focus_<target> to an id that exists in the tree")
val state = router_state("focus")
val found = handle_action(state, "focus_focus_target")
expect(found.focused_id).to_equal("focus_target")

step("Route focus_<missing> to an id that is not in the tree")
val missing = handle_action(state, "focus_focus_nope")
expect(missing.focused_id).to_equal(state.focused_id)
```

</details>

#### tab_<tabs_id>_<index> sets active_index on the named tabs widget

- Route a tab-switch action
- handle action
   - Expected: WidgetNode(id: "tab_tabs").get_prop("active_index") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Route a tab-switch action")
val state = router_state("tab")
handle_action(state, "tab_tab_tabs_2")

expect(WidgetNode(id: "tab_tabs").get_prop("active_index")).to_equal("2")
```

</details>

#### toggle_<node_id> flips the expanded prop true/false/true

- First toggle: unset -> true
- handle action
   - Expected: WidgetNode(id: "toggle_node").get_prop("expanded") equals `true`
- Second toggle: true -> false
- handle action
   - Expected: WidgetNode(id: "toggle_node").get_prop("expanded") equals `false`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("First toggle: unset -> true")
val state = router_state("toggle")
handle_action(state, "toggle_toggle_node")
expect(WidgetNode(id: "toggle_node").get_prop("expanded")).to_equal("true")

step("Second toggle: true -> false")
handle_action(state, "toggle_toggle_node")
expect(WidgetNode(id: "toggle_node").get_prop("expanded")).to_equal("false")
```

</details>

#### sort_col_<n> sets sort_column/sort_dir on the currently focused widget

- Focus the table widget, then route a sort_col_ action
- var state = router state
- state = UIState
- handle action
   - Expected: WidgetNode(id: "sort_table").get_prop("sort_column") equals `2`
   - Expected: WidgetNode(id: "sort_table").get_prop("sort_dir") equals `asc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Focus the table widget, then route a sort_col_ action")
var state = router_state("sort")
state = UIState(tree: state.tree, mode: state.mode, focused_id: "sort_table", command_buffer: state.command_buffer)
handle_action(state, "sort_col_2")

expect(WidgetNode(id: "sort_table").get_prop("sort_column")).to_equal("2")
expect(WidgetNode(id: "sort_table").get_prop("sort_dir")).to_equal("asc")
```

</details>

#### filter_<id> clears filter_text on the named widget

- Pre-seed a filter, then route the filter_ action
- WidgetNode
- handle action
   - Expected: WidgetNode(id: "filter_table").get_prop("filter_text") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pre-seed a filter, then route the filter_ action")
val state = router_state("filter")
WidgetNode(id: "filter_table").set_prop("filter_text", "stale-query")
handle_action(state, "filter_filter_table")

expect(WidgetNode(id: "filter_table").get_prop("filter_text")).to_equal("")
```

</details>

#### select_<id>_<index> sets selected_index on the named list widget

- Route a list-select action
- handle action
   - Expected: WidgetNode(id: "select_list").get_prop("selected_index") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Route a list-select action")
val state = router_state("select")
handle_action(state, "select_select_list_3")

expect(WidgetNode(id: "select_list").get_prop("selected_index")).to_equal("3")
```

</details>

#### an unrecognized action name falls through unchanged

- Route a name matching none of the known prefixes
   - Expected: result.focused_id equals `state.focused_id`
   - Expected: result.mode_name() equals `state.mode_name()`
   - Expected: result.command_buffer equals `state.command_buffer`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Route a name matching none of the known prefixes")
val state = router_state("fallthrough")
val result = handle_action(state, "no_such_prefix_xyz")

expect(result.focused_id).to_equal(state.focused_id)
expect(result.mode_name()).to_equal(state.mode_name())
expect(result.command_buffer).to_equal(state.command_buffer)
```

</details>

### process_event -> handle_pointer — pointer reducer path

#### a TouchPress over a widget moves focus to it via the public (state, event) -> state signature

- Build a one-button tree and press inside its rect
   - Expected: pressed.focused_id equals `pointer_btn`
- A TouchMove over the same widget only updates hover, not focus
   - Expected: moved.focused_id equals `pointer_btn`
   - Expected: WidgetNode(id: "pointer_btn").get_prop("ui_hover") equals `true`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Build a one-button tree and press inside its rect")
val root = column("pointer_root", [button("pointer_btn", "Click", "act")])
val state = UIState.new(build_tree(root))

val pressed = process_event(state, UIEvent.TouchPress(x: 10, y: 10))
expect(pressed.focused_id).to_equal("pointer_btn")

step("A TouchMove over the same widget only updates hover, not focus")
val moved = process_event(pressed, UIEvent.TouchMove(x: 10, y: 10))
expect(moved.focused_id).to_equal("pointer_btn")
expect(WidgetNode(id: "pointer_btn").get_prop("ui_hover")).to_equal("true")
```

</details>

### engine2d_host_gpu_lane_schedule — reject guards

#### rejects an invalid source lane

- assert false
   - Expected: result.diagnostic equals `invalid source lane`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = engine2d_host_gpu_lane_schedule("bogus", ENGINE2D_HOST_GPU_LANE_HOST, "draw_ir_delta", 256, 4096, false, false, true, 10)
assert_false(result.ok)
expect(result.diagnostic).to_equal("invalid source lane")
```

</details>

#### rejects an invalid target lane

- assert false
   - Expected: result.diagnostic equals `invalid target lane`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = engine2d_host_gpu_lane_schedule(ENGINE2D_HOST_GPU_LANE_HOST, "bogus", "draw_ir_delta", 256, 4096, false, false, true, 10)
assert_false(result.ok)
expect(result.diagnostic).to_equal("invalid target lane")
```

</details>

#### rejects a packet estimate that exceeds max_packet_bytes

- assert false
   - Expected: result.diagnostic equals `packet estimate exceeds max_packet`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = engine2d_host_gpu_lane_schedule(ENGINE2D_HOST_GPU_LANE_HOST, ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 5000, 4096, false, false, true, 10)
assert_false(result.ok)
expect(result.diagnostic).to_equal("packet estimate exceeds max_packet")
```

</details>

#### rejects a GPU target that would mutate host semantics

- assert false
   - Expected: result.diagnostic equals `GPU lane cannot mutate host semantic state`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = engine2d_host_gpu_lane_schedule(ENGINE2D_HOST_GPU_LANE_HOST, ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 256, 4096, true, false, true, 10)
assert_false(result.ok)
expect(result.diagnostic).to_equal("GPU lane cannot mutate host semantic state")
```

</details>

#### rejects per-widget GPU dispatch (must be batched)

- assert false
   - Expected: result.diagnostic equals `per-widget GPU dispatch must be batched`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = engine2d_host_gpu_lane_schedule(ENGINE2D_HOST_GPU_LANE_HOST, ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 256, 4096, false, true, true, 10)
assert_false(result.ok)
expect(result.diagnostic).to_equal("per-widget GPU dispatch must be batched")
```

</details>

#### rejects a GPU target operation that is not a coarse render/resource batch

- assert false
   - Expected: result.diagnostic equals `GPU lane operation must be a coarse render/resource batch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = engine2d_host_gpu_lane_schedule(ENGINE2D_HOST_GPU_LANE_HOST, ENGINE2D_HOST_GPU_LANE_GPU, "single_draw", 256, 4096, false, false, true, 10)
assert_false(result.ok)
expect(result.diagnostic).to_equal("GPU lane operation must be a coarse render/resource batch")
```

</details>

#### accepts a valid coarse GPU batch with honest (non-fabricated) estimated_ms

- estimated_ms must equal baseline_ms exactly -- no baseline_ms/2 fabricated speedup
- assert true
- assert true
- assert false
   - Expected: result.estimated_ms equals `result.baseline_ms`
   - Expected: result.estimated_ms equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("estimated_ms must equal baseline_ms exactly -- no baseline_ms/2 fabricated speedup")
val result = engine2d_host_gpu_lane_schedule(ENGINE2D_HOST_GPU_LANE_HOST, ENGINE2D_HOST_GPU_LANE_GPU, "draw_ir_delta", 256, 4096, false, false, true, 10)
assert_true(result.ok)
assert_true(result.gpu_batched)
assert_false(result.committed_on_host)
expect(result.estimated_ms).to_equal(result.baseline_ms)
expect(result.estimated_ms).to_equal(10)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
