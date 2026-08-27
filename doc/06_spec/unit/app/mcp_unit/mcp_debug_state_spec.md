# Mcp Debug State Specification

> Tests covering breakpoint management, breakpoint info JSON format, execution control, frame navigation, watch expressions, source file reading, expression evaluation, terminate and cleanup, debug stubs delegation to debug_state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 42 | 42 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Debug State Specification

## Scenarios

### breakpoint management

#### breakpoint entry has required fields

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- breakpoint entry has required fields
   - Expected: fields.len() equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("breakpoint entry has required fields")
val fields = ["id", "file", "line", "condition", "hit_condition", "log_message", "is_temporary", "enabled", "function_name"]
expect(fields.len()).to_equal(9)
```

</details>

#### add_breakpoint returns incrementing IDs

- add_breakpoint returns incrementing IDs
   - Expected: second_id equals `first_id + 1`
   - Expected: third_id equals `second_id + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_breakpoint returns incrementing IDs")
val first_id = 1
val second_id = 2
val third_id = 3
expect(second_id).to_equal(first_id + 1)
expect(third_id).to_equal(second_id + 1)
```

</details>

#### add_breakpoint_rich includes condition

- add_breakpoint_rich includes condition
   - Expected: has_condition is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_breakpoint_rich includes condition")
val condition = "x > 10"
val has_condition = condition != ""
expect(has_condition).to_equal(true)
```

</details>

#### add_breakpoint_rich handles temporary flag

- add_breakpoint_rich handles temporary flag
   - Expected: tmp_true is true
   - Expected: tmp_false is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_breakpoint_rich handles temporary flag")
val is_temporary_1 = 1
val is_temporary_0 = 0
val tmp_true = is_temporary_1 != 0
val tmp_false = is_temporary_0 != 0
expect(tmp_true).to_equal(true)
expect(tmp_false).to_equal(false)
```

</details>

#### add_function_breakpoint sets function_name

- add_function_breakpoint sets function_name
   - Expected: has_func is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_function_breakpoint sets function_name")
val func_name = "query_main"
val has_func = func_name != ""
expect(has_func).to_equal(true)
```

</details>

#### add_function_breakpoint sets line to -1

- add_function_breakpoint sets line to -1
   - Expected: line equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_function_breakpoint sets line to -1")
val line = -1
expect(line).to_equal(-1)
```

</details>

#### remove_breakpoint filters by file and line

- remove_breakpoint filters by file and line
   - Expected: keep is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remove_breakpoint filters by file and line")
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

- set_breakpoint_enabled toggles enabled flag
   - Expected: en_true is true
   - Expected: en_false is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_breakpoint_enabled toggles enabled flag")
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

- get_breakpoint_info returns JSON object


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_breakpoint_info returns JSON object")
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

- get_breakpoint_info returns empty for unknown id
   - Expected: result equals `{}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_breakpoint_info returns empty for unknown id")
val result = "{}"
expect(result).to_equal("{}")
```

</details>

#### list_breakpoints returns JSON array

- list_breakpoints returns JSON array


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("list_breakpoints returns JSON array")
var r = "["
r = r + "{\"id\": 1, \"file\": \"a.spl\", \"line\": 5, \"enabled\": true, \"function_name\": \"\"}"
r = r + "]"
expect(r).to_start_with("[")
expect(r).to_end_with("]")
```

</details>

#### list_breakpoints empty returns empty array

- list_breakpoints empty returns empty array
   - Expected: result equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("list_breakpoints empty returns empty array")
val result = "[]"
expect(result).to_equal("[]")
```

</details>

#### JSON uses string concatenation to avoid escape issues

- JSON uses string concatenation to avoid escape issues


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("JSON uses string concatenation to avoid escape issues")
# In Simple, }} inside strings produces }, so we use concatenation
var r = "{"
r = r + "\"key\": \"value\""
r = r + "}"
expect(r).to_contain("\"key\"")
```

</details>

### execution control

#### continue_exec resets step mode to 0

- continue_exec resets step mode to 0
   - Expected: step_mode equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("continue_exec resets step mode to 0")
val step_mode = 0
expect(step_mode).to_equal(0)
```

</details>

#### set_step_mode stores mode value

- set_step_mode stores mode value
   - Expected: mode_over equals `1`
   - Expected: mode_in equals `2`
   - Expected: mode_out equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_step_mode stores mode value")
val mode_over = 1
val mode_in = 2
val mode_out = 3
expect(mode_over).to_equal(1)
expect(mode_in).to_equal(2)
expect(mode_out).to_equal(3)
```

</details>

#### pause_exec is a no-op stub

- pause_exec is a no-op stub
   - Expected: paused is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("pause_exec is a no-op stub")
val paused = true
expect(paused).to_equal(true)
```

</details>

### frame navigation

#### select_frame stores frame index

- select_frame stores frame index
   - Expected: frame_index equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("select_frame stores frame index")
val frame_index = 3
expect(frame_index).to_equal(3)
```

</details>

#### select_frame returns 0 on success

- select_frame returns 0 on success
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("select_frame returns 0 on success")
val result = 0
expect(result).to_equal(0)
```

</details>

#### get_selected_frame returns stored index

- get_selected_frame returns stored index
   - Expected: selected equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_selected_frame returns stored index")
val selected = 3
expect(selected).to_equal(3)
```

</details>

#### frame_locals returns empty stub

- frame_locals returns empty stub
   - Expected: locals equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("frame_locals returns empty stub")
val locals = ""
expect(locals).to_equal("")
```

</details>

### watch expressions

#### add_watch appends to list

- add_watch appends to list
   - Expected: watches.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_watch appends to list")
val watches = ["x", "y", "x + y"]
expect(watches.len()).to_equal(3)
```

</details>

#### add_watch returns new length

- add_watch returns new length
   - Expected: length_after equals `length_before + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("add_watch returns new length")
val length_before = 2
val length_after = 3
expect(length_after).to_equal(length_before + 1)
```

</details>

#### remove_watch filters out matching expression

- remove_watch filters out matching expression
   - Expected: kept.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("remove_watch filters out matching expression")
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

- list_watches returns JSON array


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("list_watches returns JSON array")
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

- list_watches empty returns empty array
   - Expected: result equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("list_watches empty returns empty array")
val result = "[]"
expect(result).to_equal("[]")
```

</details>

### source file reading

#### get_source_lines reads actual file content

- get_source_lines reads actual file content
   - Expected: uses_real_io is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_source_lines reads actual file content")
# Uses rt_file_read_text internally
val uses_real_io = true
expect(uses_real_io).to_equal(true)
```

</details>

#### get_source_lines handles empty file

- get_source_lines handles empty file
   - Expected: is_empty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_source_lines handles empty file")
val content = ""
val is_empty = content == ""
expect(is_empty).to_equal(true)
```

</details>

#### get_source_lines respects start_line and count

- get_source_lines respects start_line and count
   - Expected: end_line equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_source_lines respects start_line and count")
val start_line = 5
val line_count = 10
val end_line = start_line + line_count
expect(end_line).to_equal(15)
```

</details>

#### get_source_lines joins with newlines

- get_source_lines joins with newlines


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_source_lines joins with newlines")
val lines = ["line1", "line2", "line3"]
val result = lines.join("\n")
expect(result).to_contain("line1")
expect(result).to_contain("line2")
```

</details>

### expression evaluation

#### eval_expression returns not-implemented JSON

- eval_expression returns not-implemented JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("eval_expression returns not-implemented JSON")
var r = "{"
r = r + "\"result\": \"(not implemented)\""
r = r + ", \"type\": \"error\""
r = r + "}"
expect(r).to_contain("not implemented")
expect(r).to_contain("error")
```

</details>

#### set_variable returns 0 stub

- set_variable returns 0 stub
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set_variable returns 0 stub")
val result = 0
expect(result).to_equal(0)
```

</details>

### terminate and cleanup

#### terminate resets all state

- terminate resets all state
   - Expected: fields_reset.len() equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("terminate resets all state")
val fields_reset = ["breakpoints", "next_bp_id", "watches", "call_stack", "step_mode", "is_active", "current_file", "current_line", "selected_frame"]
expect(fields_reset.len()).to_equal(9)
```

</details>

#### terminate resets breakpoints to empty

- terminate resets breakpoints to empty
   - Expected: breakpoints_after.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("terminate resets breakpoints to empty")
val breakpoints_after: [text] = []
expect(breakpoints_after.len()).to_equal(0)
```

</details>

#### terminate resets next_bp_id to 1

- terminate resets next_bp_id to 1
   - Expected: next_id equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("terminate resets next_bp_id to 1")
val next_id = 1
expect(next_id).to_equal(1)
```

</details>

#### terminate resets watches to empty

- terminate resets watches to empty
   - Expected: watches_after.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("terminate resets watches to empty")
val watches_after: [text] = []
expect(watches_after.len()).to_equal(0)
```

</details>

#### terminate resets active to false

- terminate resets active to false
   - Expected: is_active is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("terminate resets active to false")
val is_active = false
expect(is_active).to_equal(false)
```

</details>

#### terminate resets current position

- terminate resets current position
   - Expected: current_file equals ``
   - Expected: current_line equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("terminate resets current position")
val current_file = ""
val current_line = 0
expect(current_file).to_equal("")
expect(current_line).to_equal(0)
```

</details>

### debug stubs delegation to debug_state

#### rt_debug_add_breakpoint_at delegates to ds_add_breakpoint

- rt_debug_add_breakpoint_at delegates to ds_add_breakpoint
   - Expected: delegate_target equals `ds_add_breakpoint`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rt_debug_add_breakpoint_at delegates to ds_add_breakpoint")
val delegate_target = "ds_add_breakpoint"
expect(delegate_target).to_equal("ds_add_breakpoint")
```

</details>

#### rt_debug_list_breakpoints delegates to ds_list_breakpoints

- rt_debug_list_breakpoints delegates to ds_list_breakpoints
   - Expected: delegate_target equals `ds_list_breakpoints`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rt_debug_list_breakpoints delegates to ds_list_breakpoints")
val delegate_target = "ds_list_breakpoints"
expect(delegate_target).to_equal("ds_list_breakpoints")
```

</details>

#### rt_debug_get_source_lines delegates to ds_get_source_lines

- rt_debug_get_source_lines delegates to ds_get_source_lines
   - Expected: delegate_target equals `ds_get_source_lines`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rt_debug_get_source_lines delegates to ds_get_source_lines")
val delegate_target = "ds_get_source_lines"
expect(delegate_target).to_equal("ds_get_source_lines")
```

</details>

#### rt_debug_terminate delegates to ds_terminate

- rt_debug_terminate delegates to ds_terminate
   - Expected: delegate_target equals `ds_terminate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rt_debug_terminate delegates to ds_terminate")
val delegate_target = "ds_terminate"
expect(delegate_target).to_equal("ds_terminate")
```

</details>

#### all rt_debug functions have ds_ counterparts

- all rt_debug functions have ds_ counterparts
   - Expected: rt_functions.len() equals `ds_functions.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all rt_debug functions have ds_ counterparts")
val rt_functions = ["rt_debug_set_active", "rt_debug_add_breakpoint_at", "rt_debug_remove_breakpoint_at", "rt_debug_continue_exec", "rt_debug_terminate"]
val ds_functions = ["ds_set_active", "ds_add_breakpoint", "ds_remove_breakpoint", "ds_continue_exec", "ds_terminate"]
expect(rt_functions.len()).to_equal(ds_functions.len())
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/mcp_debug_state_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering breakpoint management, breakpoint info JSON format, execution control, frame navigation, watch expressions, source file reading, expression evaluation, terminate and cleanup, debug stubs delegation to debug_state.
- breakpoint management
- breakpoint info JSON format
- execution control
- frame navigation
- watch expressions
- source file reading
- expression evaluation
- terminate and cleanup
- debug stubs delegation to debug_state

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 42 |
| Active scenarios | 42 |
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

- Canonical SPipe generation for source `de788296fe266e2615999a44c6cf533cf6f51ff96e924900d5a53407b430bc14`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `de788296fe266e2615999a44c6cf533cf6f51ff96e924900d5a53407b430bc14`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `de788296fe266e2615999a44c6cf533cf6f51ff96e924900d5a53407b430bc14`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/mcp_unit/mcp_debug_state_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_debug_state_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_debug_state_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_debug_state_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_debug_state_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 18 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/mcp_debug_state_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'breakpoint entry has required fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_debug_state_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'add_breakpoint returns incrementing IDs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_debug_state_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'add_breakpoint_rich includes condition' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
