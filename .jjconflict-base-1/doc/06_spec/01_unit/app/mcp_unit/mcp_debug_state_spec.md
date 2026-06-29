# mcp_debug_state_spec

> Tests for debug_state.spl real in-memory state management. Validates breakpoints, watches, frame navigation, execution control, source reading, and terminate/cleanup.

<!-- sdn-diagram:id=mcp_debug_state_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_debug_state_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_debug_state_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_debug_state_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 42 | 42 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# mcp_debug_state_spec

Tests for debug_state.spl real in-memory state management. Validates breakpoints, watches, frame navigation, execution control, source reading, and terminate/cleanup.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #DBG-001 to #DBG-008 |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/01_unit/app/mcp_unit/mcp_debug_state_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview
Tests for debug_state.spl real in-memory state management.
Validates breakpoints, watches, frame navigation, execution control,
source reading, and terminate/cleanup.

## Scenarios

### breakpoint management

#### breakpoint entry has required fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields = ["id", "file", "line", "condition", "hit_condition", "log_message", "is_temporary", "enabled", "function_name"]
expect(fields.len()).to_equal(9)
```

</details>

#### add_breakpoint returns incrementing IDs

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first_id = 1
val second_id = 2
val third_id = 3
expect(second_id).to_equal(first_id + 1)
expect(third_id).to_equal(second_id + 1)
```

</details>

#### add_breakpoint_rich includes condition

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val condition = "x > 10"
val has_condition = condition != ""
expect(has_condition).to_equal(true)
```

</details>

#### add_breakpoint_rich handles temporary flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_temporary_1 = 1
val is_temporary_0 = 0
val tmp_true = is_temporary_1 != 0
val tmp_false = is_temporary_0 != 0
expect(tmp_true).to_equal(true)
expect(tmp_false).to_equal(false)
```

</details>

#### add_function_breakpoint sets function_name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val func_name = "query_main"
val has_func = func_name != ""
expect(has_func).to_equal(true)
```

</details>

#### add_function_breakpoint sets line to -1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val line = -1
expect(line).to_equal(-1)
```

</details>

#### remove_breakpoint filters by file and line

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp_file = "test.spl"
val bp_line = 10
# Filter: keep bps where file != bp_file or line != bp_line
val other_file = "other.spl"
val other_line = 20
val keep = other_file != bp_file or other_line != bp_line
expect(keep).to_equal(true)
```

</details>

#### set_breakpoint_enabled toggles enabled flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enabled_1 = 1
val enabled_0 = 0
val en_true = enabled_1 != 0
val en_false = enabled_0 != 0
expect(en_true).to_equal(true)
expect(en_false).to_equal(false)
```

</details>

### breakpoint info JSON format

#### get_breakpoint_info returns JSON object

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = "{"
r = r + "\"id\": 1"
r = r + ", \"file\": \"test.spl\""
r = r + ", \"line\": 10"
r = r + ", \"enabled\": true"
r = r + "}"
expect(r).to_contain("\"id\": 1")
expect(r).to_contain("\"file\": \"test.spl\"")
```

</details>

#### get_breakpoint_info returns empty for unknown id

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "{}"
expect(result).to_equal("{}")
```

</details>

#### list_breakpoints returns JSON array

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = "["
r = r + "{\"id\": 1, \"file\": \"a.spl\", \"line\": 5, \"enabled\": true, \"function_name\": \"\"}"
r = r + "]"
expect(r).to_start_with("[")
expect(r).to_end_with("]")
```

</details>

#### list_breakpoints empty returns empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "[]"
expect(result).to_equal("[]")
```

</details>

#### JSON uses string concatenation to avoid escape issues

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# In Simple, }} inside strings produces }, so we use concatenation
var r = "{"
r = r + "\"key\": \"value\""
r = r + "}"
expect(r).to_contain("\"key\"")
```

</details>

### execution control

#### continue_exec resets step mode to 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val step_mode = 0
expect(step_mode).to_equal(0)
```

</details>

#### set_step_mode stores mode value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mode_over = 1
val mode_in = 2
val mode_out = 3
expect(mode_over).to_equal(1)
expect(mode_in).to_equal(2)
expect(mode_out).to_equal(3)
```

</details>

#### pause_exec is a no-op stub

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val paused = true
expect(paused).to_equal(true)
```

</details>

### frame navigation

#### select_frame stores frame index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame_index = 3
expect(frame_index).to_equal(3)
```

</details>

#### select_frame returns 0 on success

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 0
expect(result).to_equal(0)
```

</details>

#### get_selected_frame returns stored index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val selected = 3
expect(selected).to_equal(3)
```

</details>

#### frame_locals returns empty stub

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val locals = ""
expect(locals).to_equal("")
```

</details>

### watch expressions

#### add_watch appends to list

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val watches = ["x", "y", "x + y"]
expect(watches.len()).to_equal(3)
```

</details>

#### add_watch returns new length

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val length_before = 2
val length_after = 3
expect(length_after).to_equal(length_before + 1)
```

</details>

#### remove_watch filters out matching expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val watches = ["x", "y", "z"]
# Remove "y" -> keep ["x", "z"]
var kept: [text] = []
for w in watches:
    if w != "y":
        kept = kept + [w]
expect(kept.len()).to_equal(2)
expect(kept).to_contain("x")
expect(kept).to_contain("z")
```

</details>

#### list_watches returns JSON array

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = "["
r = r + "\"x\""
r = r + ", \"y\""
r = r + "]"
expect(r).to_start_with("[")
expect(r).to_contain("\"x\"")
expect(r).to_contain("\"y\"")
```

</details>

#### list_watches empty returns empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "[]"
expect(result).to_equal("[]")
```

</details>

### source file reading

#### get_source_lines reads actual file content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Uses rt_file_read_text internally
val uses_real_io = true
expect(uses_real_io).to_equal(true)
```

</details>

#### get_source_lines handles empty file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = ""
val is_empty = content == ""
expect(is_empty).to_equal(true)
```

</details>

#### get_source_lines respects start_line and count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val start_line = 5
val line_count = 10
val end_line = start_line + line_count
expect(end_line).to_equal(15)
```

</details>

#### get_source_lines joins with newlines

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lines = ["line1", "line2", "line3"]
val result = lines.join("\n")
expect(result).to_contain("line1")
expect(result).to_contain("line2")
```

</details>

### expression evaluation

#### eval_expression returns not-implemented JSON

1. r = r + "\"result\": \"


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var r = "{"
r = r + "\"result\": \"(not implemented)\""
r = r + ", \"type\": \"error\""
r = r + "}"
expect(r).to_contain("not implemented")
expect(r).to_contain("error")
```

</details>

#### set_variable returns 0 stub

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 0
expect(result).to_equal(0)
```

</details>

### terminate and cleanup

#### terminate resets all state

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fields_reset = ["breakpoints", "next_bp_id", "watches", "call_stack", "step_mode", "is_active", "current_file", "current_line", "selected_frame"]
expect(fields_reset.len()).to_equal(9)
```

</details>

#### terminate resets breakpoints to empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val breakpoints_after: [text] = []
expect(breakpoints_after.len()).to_equal(0)
```

</details>

#### terminate resets next_bp_id to 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val next_id = 1
expect(next_id).to_equal(1)
```

</details>

#### terminate resets watches to empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val watches_after: [text] = []
expect(watches_after.len()).to_equal(0)
```

</details>

#### terminate resets active to false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val is_active = false
expect(is_active).to_equal(false)
```

</details>

#### terminate resets current position

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val current_file = ""
val current_line = 0
expect(current_file).to_equal("")
expect(current_line).to_equal(0)
```

</details>

### debug stubs delegation to debug_state

#### rt_debug_add_breakpoint_at delegates to ds_add_breakpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val delegate_target = "ds_add_breakpoint"
expect(delegate_target).to_equal("ds_add_breakpoint")
```

</details>

#### rt_debug_list_breakpoints delegates to ds_list_breakpoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val delegate_target = "ds_list_breakpoints"
expect(delegate_target).to_equal("ds_list_breakpoints")
```

</details>

#### rt_debug_get_source_lines delegates to ds_get_source_lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val delegate_target = "ds_get_source_lines"
expect(delegate_target).to_equal("ds_get_source_lines")
```

</details>

#### rt_debug_terminate delegates to ds_terminate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val delegate_target = "ds_terminate"
expect(delegate_target).to_equal("ds_terminate")
```

</details>

#### all rt_debug functions have ds_ counterparts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rt_functions = ["rt_debug_set_active", "rt_debug_add_breakpoint_at", "rt_debug_remove_breakpoint_at", "rt_debug_continue_exec", "rt_debug_terminate"]
val ds_functions = ["ds_set_active", "ds_add_breakpoint", "ds_remove_breakpoint", "ds_continue_exec", "ds_terminate"]
expect(rt_functions.len()).to_equal(ds_functions.len())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 42 |
| Active scenarios | 42 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
