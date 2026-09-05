# DAP Step Modes

> Tests the Debug Adapter Protocol stepping modes including step-in, step-over, step-out, and step-back. Verifies that each step mode advances execution to the correct source location respecting function boundaries and call depth.

<!-- sdn-diagram:id=step_modes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=step_modes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

step_modes_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=step_modes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DAP Step Modes

Tests the Debug Adapter Protocol stepping modes including step-in, step-over, step-out, and step-back. Verifies that each step mode advances execution to the correct source location respecting function boundaries and call depth.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Developer Tools |
| Status | In Progress |
| Source | `test/03_system/feature/dap/step_modes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the Debug Adapter Protocol stepping modes including step-in, step-over,
step-out, and step-back. Verifies that each step mode advances execution to
the correct source location respecting function boundaries and call depth.

## Scenarios

### Step Modes

### Mode 0: Continue

#### sets continue mode

1. debug set active
2. debug set step mode
   - Expected: mode equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_step_mode(0)

val mode = debug_get_step_mode()
expect(mode).to_equal(0)
```

</details>

#### does not break without breakpoint

1. debug set active
2. debug set step mode
3. debug set current location
   - Expected: should_break is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_step_mode(0)
debug_set_current_location("test.spl", 10, 0)

val should_break = debug_should_break()
expect(should_break).to_equal(false)
```

</details>

### Mode 1: Step Over

#### sets step over mode

1. debug set active
2. debug set step mode
   - Expected: mode equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_step_mode(1)

val mode = debug_get_step_mode()
expect(mode).to_equal(1)
```

</details>

#### breaks at same depth

1. reset state
2. debug set active
3. debug set step mode
4. debug set step start depth
5. debug push frame
6. debug push frame
7. debug push frame
8. debug push frame
9. debug push frame
10. debug set current location
   - Expected: should_break is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)
debug_set_step_mode(1)
debug_set_step_start_depth(5)

# Simulate being at depth 5
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)

debug_set_current_location("test.spl", 11, 0)
val should_break = debug_should_break()
expect(should_break).to_equal(true)
```

</details>

#### breaks at lower depth

1. reset state
2. debug set active
3. debug set step mode
4. debug set step start depth
5. debug push frame
6. debug push frame
7. debug push frame
8. debug set current location
   - Expected: should_break is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)
debug_set_step_mode(1)
debug_set_step_start_depth(5)

# Simulate being at depth 3 (returned from function)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)

debug_set_current_location("test.spl", 15, 0)
val should_break = debug_should_break()
expect(should_break).to_equal(true)
```

</details>

#### does not break at higher depth

1. reset state
2. debug set active
3. debug set step mode
4. debug set step start depth
5. debug push frame
6. debug push frame
7. debug push frame
8. debug push frame
9. debug push frame
10. debug set current location
   - Expected: should_break is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)
debug_set_step_mode(1)
debug_set_step_start_depth(3)

# Simulate being at depth 5 (inside function call)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)

debug_set_current_location("test.spl", 12, 0)
val should_break = debug_should_break()
expect(should_break).to_equal(false)
```

</details>

### Mode 2: Step Into

#### sets step into mode

1. debug set active
2. debug set step mode
   - Expected: mode equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_step_mode(2)

val mode = debug_get_step_mode()
expect(mode).to_equal(2)
```

</details>

#### breaks at any depth - same level

1. debug set active
2. debug set step mode
3. debug set current location
   - Expected: should_break is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_step_mode(2)
debug_set_current_location("test.spl", 10, 0)

val should_break = debug_should_break()
expect(should_break).to_equal(true)
```

</details>

#### breaks at any depth - deeper

1. reset state
2. debug set active
3. debug set step mode
4. debug push frame
5. debug set current location
   - Expected: should_break is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)
debug_set_step_mode(2)

debug_push_frame("func", "test.spl", 20, 0)
debug_set_current_location("test.spl", 21, 0)

val should_break = debug_should_break()
expect(should_break).to_equal(true)
```

</details>

#### breaks at any depth - shallower

1. reset state
2. debug set active
3. debug set step mode
4. debug push frame
5. debug pop frame
6. debug set current location
   - Expected: should_break is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)
debug_set_step_mode(2)
debug_push_frame("func", "test.spl", 20, 0)
debug_pop_frame()  # Return from function

debug_set_current_location("test.spl", 11, 0)
val should_break = debug_should_break()
expect(should_break).to_equal(true)
```

</details>

### Mode 3: Step Out

#### sets step out mode

1. debug set active
2. debug set step mode
   - Expected: mode equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_step_mode(3)

val mode = debug_get_step_mode()
expect(mode).to_equal(3)
```

</details>

#### breaks at lower depth

1. reset state
2. debug set active
3. debug set step mode
4. debug set step start depth
5. debug push frame
6. debug push frame
7. debug push frame
8. debug set current location
   - Expected: should_break is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)
debug_set_step_mode(3)
debug_set_step_start_depth(5)

# Simulate at depth 3 (returned)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)

debug_set_current_location("test.spl", 50, 0)
val should_break = debug_should_break()
expect(should_break).to_equal(true)
```

</details>

#### does not break at same depth

1. reset state
2. debug set active
3. debug set step mode
4. debug set step start depth
5. debug push frame
6. debug push frame
7. debug push frame
8. debug push frame
9. debug push frame
10. debug set current location
   - Expected: should_break is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)
debug_set_step_mode(3)
debug_set_step_start_depth(5)

# Simulate at depth 5 (same level)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)

debug_set_current_location("test.spl", 51, 0)
val should_break = debug_should_break()
expect(should_break).to_equal(false)
```

</details>

#### does not break at higher depth

1. reset state
2. debug set active
3. debug set step mode
4. debug set step start depth
5. debug push frame
6. debug push frame
7. debug push frame
8. debug push frame
9. debug push frame
10. debug set current location
   - Expected: should_break is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)
debug_set_step_mode(3)
debug_set_step_start_depth(3)

# Simulate at depth 5 (deeper)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)

debug_set_current_location("test.spl", 52, 0)
val should_break = debug_should_break()
expect(should_break).to_equal(false)
```

</details>

### Step mode transitions

#### transitions from Continue to StepOver

1. debug set active
2. debug set step mode
   - Expected: debug_get_step_mode() equals `0`
3. debug set step mode
   - Expected: debug_get_step_mode() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_step_mode(0)
expect(debug_get_step_mode()).to_equal(0)

debug_set_step_mode(1)
expect(debug_get_step_mode()).to_equal(1)
```

</details>

#### transitions from StepOver to StepInto

1. debug set active
2. debug set step mode
3. debug set step mode
   - Expected: debug_get_step_mode() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_step_mode(1)
debug_set_step_mode(2)
expect(debug_get_step_mode()).to_equal(2)
```

</details>

#### transitions from StepInto to StepOut

1. debug set active
2. debug set step mode
3. debug set step mode
   - Expected: debug_get_step_mode() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_step_mode(2)
debug_set_step_mode(3)
expect(debug_get_step_mode()).to_equal(3)
```

</details>

#### returns to Continue after step completes

1. debug set active
2. debug set step mode
3. debug set step mode
   - Expected: debug_get_step_mode() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_step_mode(1)
# After step completes, mode should reset to 0
debug_set_step_mode(0)
expect(debug_get_step_mode()).to_equal(0)
```

</details>

### Depth tracking

#### tracks depth correctly

1. reset state
2. debug set active
   - Expected: debug_stack_depth() equals `0`
3. debug push frame
   - Expected: debug_stack_depth() equals `1`
4. debug push frame
   - Expected: debug_stack_depth() equals `2`
5. debug pop frame
   - Expected: debug_stack_depth() equals `1`
6. debug pop frame
   - Expected: debug_stack_depth() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)
expect(debug_stack_depth()).to_equal(0)

debug_push_frame("func1", "test.spl", 10, 0)
expect(debug_stack_depth()).to_equal(1)

debug_push_frame("func2", "test.spl", 20, 0)
expect(debug_stack_depth()).to_equal(2)

debug_pop_frame()
expect(debug_stack_depth()).to_equal(1)

debug_pop_frame()
expect(debug_stack_depth()).to_equal(0)
```

</details>

#### stores and retrieves start depth

1. debug set active
2. debug set step start depth
   - Expected: debug_get_step_start_depth() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_step_start_depth(42)
expect(debug_get_step_start_depth()).to_equal(42)
```

</details>

### Interaction with breakpoints

#### breakpoints override continue mode

1. debug set active
2. debug set step mode
3. debug add breakpoint
4. debug set current location
   - Expected: should_break is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_step_mode(0)  # Continue
debug_add_breakpoint("test.spl", 10, 1)
debug_set_current_location("test.spl", 10, 0)

val should_break = debug_should_break()
expect(should_break).to_equal(true)
```

</details>

#### breakpoints work with step modes

1. reset state
2. debug set active
3. debug set step mode
4. debug set step start depth
5. debug add breakpoint
6. debug push frame
7. debug push frame
8. debug push frame
9. debug set current location
   - Expected: should_break is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)
debug_set_step_mode(1)  # StepOver
debug_set_step_start_depth(5)
debug_add_breakpoint("test.spl", 15, 1)

# At depth 3, on breakpoint line
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)
debug_set_current_location("test.spl", 15, 0)

val should_break = debug_should_break()
expect(should_break).to_equal(true)
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


</details>
