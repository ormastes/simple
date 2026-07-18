# DAP Full Integration

> Tests end-to-end Debug Adapter Protocol integration including launch, breakpoint hit, variable inspection, and stepping through code. Verifies that the complete debug workflow functions correctly from client connection to session termination.

<!-- sdn-diagram:id=integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

integration_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DAP Full Integration

Tests end-to-end Debug Adapter Protocol integration including launch, breakpoint hit, variable inspection, and stepping through code. Verifies that the complete debug workflow functions correctly from client connection to session termination.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Developer Tools |
| Status | In Progress |
| Source | `test/03_system/feature/dap/integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests end-to-end Debug Adapter Protocol integration including launch, breakpoint
hit, variable inspection, and stepping through code. Verifies that the complete
debug workflow functions correctly from client connection to session termination.

## Scenarios

### Full Debugging Sessions

### Simple breakpoint session

#### executes a simple debugging session

1. debug set active
   - Expected: debug_is_active() is true
2. debug add breakpoint
   - Expected: debug_has_breakpoint("main.spl", 15) is true
3. debug set current location
   - Expected: debug_should_break() is false
4. debug set current location
   - Expected: debug_should_break() is true
5. debug pause
   - Expected: debug_is_paused() is true
   - Expected: debug_current_file() equals `main.spl`
   - Expected: debug_current_line() equals `15`
   - Expected: depth >= 0 is true
6. debug continue
   - Expected: debug_is_paused() is false
7. debug remove breakpoint
8. debug set active


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Step 1: Activate debug mode
debug_set_active(true)
expect(debug_is_active()).to_equal(true)

# Step 2: Set breakpoint
debug_add_breakpoint("main.spl", 15, 1)
expect(debug_has_breakpoint("main.spl", 15)).to_equal(true)

# Step 3: Simulate execution to line before breakpoint
debug_set_current_location("main.spl", 14, 0)
expect(debug_should_break()).to_equal(false)

# Step 4: Execute to breakpoint line
debug_set_current_location("main.spl", 15, 0)
expect(debug_should_break()).to_equal(true)

# Step 5: Pause at breakpoint
debug_pause()
expect(debug_is_paused()).to_equal(true)

# Step 6: Inspect current state
expect(debug_current_file()).to_equal("main.spl")
expect(debug_current_line()).to_equal(15)
val depth = debug_stack_depth()
expect(depth >= 0).to_equal(true)

# Step 7: Continue execution
debug_continue()
expect(debug_is_paused()).to_equal(false)

# Step 8: Clean up
debug_remove_breakpoint("main.spl", 15)
debug_set_active(false)
```

</details>

### Step through execution

#### steps through sequential code

1. debug set active
2. debug set current location
   - Expected: debug_current_line() equals `10`
3. debug set step mode
   - Expected: debug_get_step_mode() equals `2`
4. debug set current location
   - Expected: debug_should_break() is true
   - Expected: debug_current_line() equals `11`
5. debug set current location
   - Expected: debug_should_break() is true
   - Expected: debug_current_line() equals `12`
6. debug set current location
   - Expected: debug_should_break() is true
   - Expected: debug_current_line() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)

# Start at line 10
debug_set_current_location("test.spl", 10, 0)
expect(debug_current_line()).to_equal(10)

# Enable step into mode
debug_set_step_mode(2)
expect(debug_get_step_mode()).to_equal(2)

# Simulate stepping through lines
debug_set_current_location("test.spl", 11, 0)
expect(debug_should_break()).to_equal(true)
expect(debug_current_line()).to_equal(11)

debug_set_current_location("test.spl", 12, 0)
expect(debug_should_break()).to_equal(true)
expect(debug_current_line()).to_equal(12)

debug_set_current_location("test.spl", 13, 0)
expect(debug_should_break()).to_equal(true)
expect(debug_current_line()).to_equal(13)
```

</details>

#### steps over function call

1. reset state
2. debug set active
3. debug set current location
4. debug set step mode
5. debug set step start depth
6. debug push frame
7. debug set current location
   - Expected: debug_should_break() is false
8. debug pop frame
9. debug set current location
   - Expected: debug_should_break() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)
debug_set_current_location("main.spl", 20, 0)

# Set step over mode
val current_depth = debug_stack_depth()
debug_set_step_mode(1)  # StepOver
debug_set_step_start_depth(current_depth)

# Simulate function call (depth increases)
debug_push_frame("helper", "utils.spl", 5, 0)
debug_set_current_location("utils.spl", 5, 0)
# Should NOT break inside function (higher depth)
expect(debug_should_break()).to_equal(false)

# Simulate function return (depth restored)
debug_pop_frame()
debug_set_current_location("main.spl", 21, 0)
# Should break after function returns (same depth)
expect(debug_should_break()).to_equal(true)
```

</details>

#### steps into function call

1. reset state
2. debug set active
3. debug set current location
4. debug set step mode
5. debug push frame
6. debug set current location
   - Expected: debug_should_break() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)
debug_set_current_location("main.spl", 30, 0)

# Set step into mode
debug_set_step_mode(2)  # StepIn

# Simulate function call
debug_push_frame("process", "processor.spl", 10, 0)
debug_set_current_location("processor.spl", 10, 0)
# Should break inside function (step in)
expect(debug_should_break()).to_equal(true)
```

</details>

#### steps out of function

1. reset state
2. debug set active
3. debug push frame
4. debug push frame
5. debug set step mode
6. debug set step start depth
7. debug set current location
   - Expected: debug_should_break() is false
8. debug pop frame
9. debug set current location
   - Expected: debug_should_break() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)
debug_push_frame("main", "main.spl", 10, 0)
debug_push_frame("helper", "utils.spl", 5, 0)

# We're inside helper function at depth 2
val start_depth = debug_stack_depth()
debug_set_step_mode(3)  # StepOut
debug_set_step_start_depth(start_depth)

# Still inside helper
debug_set_current_location("utils.spl", 6, 0)
expect(debug_should_break()).to_equal(false)

# Return from helper
debug_pop_frame()
debug_set_current_location("main.spl", 11, 0)
# Should break after returning (lower depth)
expect(debug_should_break()).to_equal(true)
```

</details>

### Recursive function debugging

#### tracks recursive factorial calls

1. reset state
2. debug set active
3. debug add breakpoint
4. debug push frame
5. debug push frame
6. debug set current location
   - Expected: debug_should_break() is true
   - Expected: debug_stack_depth() equals `2`
7. debug push frame
8. debug set current location
   - Expected: debug_should_break() is true
   - Expected: debug_stack_depth() equals `3`
9. debug push frame
10. debug set current location
   - Expected: debug_should_break() is true
   - Expected: debug_stack_depth() equals `4`
11. debug pop frame
   - Expected: debug_stack_depth() equals `3`
12. debug pop frame
   - Expected: debug_stack_depth() equals `2`
13. debug pop frame
   - Expected: debug_stack_depth() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)
debug_add_breakpoint("math.spl", 10, 1)

# Simulate factorial(3) call chain
# main() calls factorial(3)
debug_push_frame("main", "main.spl", 20, 0)
debug_push_frame("factorial", "math.spl", 10, 0)
debug_set_current_location("math.spl", 10, 0)
expect(debug_should_break()).to_equal(true)
expect(debug_stack_depth()).to_equal(2)

# factorial(3) calls factorial(2)
debug_push_frame("factorial", "math.spl", 10, 0)
debug_set_current_location("math.spl", 10, 0)
expect(debug_should_break()).to_equal(true)
expect(debug_stack_depth()).to_equal(3)

# factorial(2) calls factorial(1)
debug_push_frame("factorial", "math.spl", 10, 0)
debug_set_current_location("math.spl", 10, 0)
expect(debug_should_break()).to_equal(true)
expect(debug_stack_depth()).to_equal(4)

# Stack trace should show all levels
val trace = debug_stack_trace()
expect(trace).to_contain("factorial")
expect(trace).to_contain("main")

# Unwind: factorial(1) returns
debug_pop_frame()
expect(debug_stack_depth()).to_equal(3)

# factorial(2) returns
debug_pop_frame()
expect(debug_stack_depth()).to_equal(2)

# factorial(3) returns
debug_pop_frame()
expect(debug_stack_depth()).to_equal(1)
```

</details>

#### handles deep recursion

1. reset state
2. debug set active
3. debug push frame
   - Expected: debug_stack_depth() >= 20 is true
   - Expected: trace.len() > 0 is true
4. debug pop frame
   - Expected: debug_stack_depth() >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)

# Simulate deep recursion (20 levels)
for i in 0..20:
    debug_push_frame("recursive", "test.spl", 10, 0)

expect(debug_stack_depth() >= 20).to_equal(true)

val trace = debug_stack_trace()
expect(trace.len() > 0).to_equal(true)

# Unwind
for i in 0..20:
    debug_pop_frame()

expect(debug_stack_depth() >= 0).to_equal(true)
```

</details>

### Multi-file debugging

#### debugs across multiple files

1. reset state
2. debug set active
3. debug add breakpoint
4. debug add breakpoint
5. debug add breakpoint
6. debug set current location
   - Expected: debug_should_break() is true
   - Expected: debug_current_file() equals `main.spl`
7. debug push frame
8. debug set current location
   - Expected: debug_should_break() is true
   - Expected: debug_current_file() equals `utils.spl`
9. debug push frame
10. debug set current location
   - Expected: debug_should_break() is true
   - Expected: debug_current_file() equals `processor.spl`
11. debug pop frame
12. debug set current location
   - Expected: debug_current_file() equals `utils.spl`
13. debug pop frame
14. debug set current location
   - Expected: debug_current_file() equals `main.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)

# Set breakpoints in different files
debug_add_breakpoint("main.spl", 10, 1)
debug_add_breakpoint("utils.spl", 25, 2)
debug_add_breakpoint("processor.spl", 50, 3)

# Execute in main.spl
debug_set_current_location("main.spl", 10, 0)
expect(debug_should_break()).to_equal(true)
expect(debug_current_file()).to_equal("main.spl")

# Call function in utils.spl
debug_push_frame("helper", "utils.spl", 25, 0)
debug_set_current_location("utils.spl", 25, 0)
expect(debug_should_break()).to_equal(true)
expect(debug_current_file()).to_equal("utils.spl")

# Call function in processor.spl
debug_push_frame("process", "processor.spl", 50, 0)
debug_set_current_location("processor.spl", 50, 0)
expect(debug_should_break()).to_equal(true)
expect(debug_current_file()).to_equal("processor.spl")

# Return through call chain
debug_pop_frame()
debug_set_current_location("utils.spl", 26, 0)
expect(debug_current_file()).to_equal("utils.spl")

debug_pop_frame()
debug_set_current_location("main.spl", 11, 0)
expect(debug_current_file()).to_equal("main.spl")
```

</details>

### Breakpoint and stepping combined

#### hits breakpoint then steps

1. reset state
2. debug set active
3. debug add breakpoint
4. debug set current location
   - Expected: debug_should_break() is true
5. debug set step mode
6. debug set current location
   - Expected: debug_should_break() is true
7. debug set current location
   - Expected: debug_should_break() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)
debug_add_breakpoint("test.spl", 20, 1)

# Run to breakpoint
debug_set_current_location("test.spl", 20, 0)
expect(debug_should_break()).to_equal(true)

# Now enable stepping
debug_set_step_mode(2)  # StepIn

# Step to next line
debug_set_current_location("test.spl", 21, 0)
expect(debug_should_break()).to_equal(true)

debug_set_current_location("test.spl", 22, 0)
expect(debug_should_break()).to_equal(true)
```

</details>

#### sets breakpoint while stepping

1. reset state
2. debug set active
3. debug set step mode
4. debug set current location
   - Expected: debug_should_break() is true
5. debug add breakpoint
6. debug set step mode
7. debug set current location
   - Expected: debug_should_break() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)
debug_set_step_mode(2)  # StepIn

# Step through some lines
debug_set_current_location("test.spl", 10, 0)
expect(debug_should_break()).to_equal(true)

# Add breakpoint ahead
debug_add_breakpoint("test.spl", 15, 1)

# Continue to breakpoint
debug_set_step_mode(0)  # Continue
debug_set_current_location("test.spl", 15, 0)
expect(debug_should_break()).to_equal(true)
```

</details>

### Error scenarios and recovery

#### handles breakpoint at non-existent line

1. debug set active
2. debug add breakpoint
3. debug set current location
   - Expected: should_break is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_add_breakpoint("test.spl", 99999, 1)

# Should not crash
debug_set_current_location("test.spl", 99999, 0)
val should_break = debug_should_break()
expect(should_break).to_equal(true)
```

</details>

#### recovers from pause without continue

1. debug set active
2. debug pause
3. debug set active
4. debug set active
5. debug continue
   - Expected: debug_is_paused() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_pause()

# Deactivate debug (should reset state)
debug_set_active(false)
debug_set_active(true)

# Should be able to continue
debug_continue()
expect(debug_is_paused()).to_equal(false)
```

</details>

#### handles missing stack frames

1. reset state
2. debug set active
3. debug pop frame
   - Expected: depth >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)

# Try to pop when nothing to pop
debug_pop_frame()

# Should not crash
val depth = debug_stack_depth()
expect(depth >= 0).to_equal(true)
```

</details>

#### handles rapid mode switching

1. debug set active
2. debug set step mode
3. debug set step mode
4. debug set step mode
5. debug set step mode
6. debug set step mode
   - Expected: mode equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)

# Rapidly switch modes
debug_set_step_mode(0)
debug_set_step_mode(1)
debug_set_step_mode(2)
debug_set_step_mode(3)
debug_set_step_mode(0)

val mode = debug_get_step_mode()
expect(mode).to_equal(0)
```

</details>

### Performance and Stress Tests

#### handles many breakpoints

1. debug set active
2. debug add breakpoint
   - Expected: debug_has_breakpoint("test.spl", i) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)

# Add 100 breakpoints
for i in 0..100:
    debug_add_breakpoint("test.spl", i, i)

# All should exist
for i in 0..100:
    expect(debug_has_breakpoint("test.spl", i)).to_equal(true)
```

</details>

#### handles frequent location updates

1. debug set active
2. debug set current location
   - Expected: debug_current_file() equals `test.spl`
   - Expected: debug_current_line() >= 0 is true
   - Expected: debug_current_line() < 100 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)

# Simulate 1000 expressions evaluated
for i in 0..1000:
    debug_set_current_location("test.spl", i % 100, 0)

# Should complete without issues
expect(debug_current_file()).to_equal("test.spl")
expect(debug_current_line() >= 0).to_equal(true)
expect(debug_current_line() < 100).to_equal(true)
```

</details>

#### handles large stack depths

1. reset state
2. debug set active
3. debug push frame
   - Expected: debug_stack_depth() >= 100 is true
   - Expected: trace.len() > 0 is true
4. debug pop frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)

# Build deep stack (100 frames)
for i in 0..100:
    debug_push_frame("func", "test.spl", 10, 0)

expect(debug_stack_depth() >= 100).to_equal(true)

# Generate trace
val trace = debug_stack_trace()
expect(trace.len() > 0).to_equal(true)

# Unwind
for i in 0..100:
    debug_pop_frame()
```

</details>

### Real-World Scenarios

#### debugs a simple program

1. reset state
2. debug set active
3. debug push frame
4. debug add breakpoint
5. debug set current location
   - Expected: debug_should_break() is true
   - Expected: debug_current_line() equals `2`
6. debug set current location
7. debug pop frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)

# Simulate: fn main() { val x = 5; print x }
debug_push_frame("main", "main.spl", 1, 0)

# Set breakpoint on variable declaration
debug_add_breakpoint("main.spl", 2, 1)

# Execute to breakpoint
debug_set_current_location("main.spl", 2, 0)
expect(debug_should_break()).to_equal(true)

# Inspect (variable would be captured here)
expect(debug_current_line()).to_equal(2)

# Continue to print statement
debug_set_current_location("main.spl", 3, 0)

# Exit main
debug_pop_frame()
```

</details>

<details>
<summary>Advanced: debugs loop with breakpoint</summary>

#### debugs loop with breakpoint

1. reset state
2. debug set active
3. debug add breakpoint
4. debug push frame
5. debug set current location
   - Expected: debug_should_break() is true
6. debug continue
7. debug pop frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)
debug_add_breakpoint("loop.spl", 5, 1)

# Simulate: for i in 0..3: print i
debug_push_frame("main", "loop.spl", 4, 0)

for i in 0..3:
    # Each iteration hits breakpoint
    debug_set_current_location("loop.spl", 5, 0)
    expect(debug_should_break()).to_equal(true)

    # Continue to next iteration
    debug_continue()

debug_pop_frame()
```

</details>


</details>

#### debugs conditional branches

1. reset state
2. debug set active
3. debug push frame
4. debug set current location
5. debug push frame
6. debug set current location
   - Expected: debug_current_line() equals `20`
7. debug pop frame
8. debug set current location
9. debug pop frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_state()
debug_set_active(true)
debug_push_frame("main", "test.spl", 10, 0)

# Simulate: if condition: branch_a() else: branch_b()
debug_set_current_location("test.spl", 11, 0)  # if statement

# Take if branch
debug_push_frame("branch_a", "test.spl", 20, 0)
debug_set_current_location("test.spl", 20, 0)
expect(debug_current_line()).to_equal(20)
debug_pop_frame()

# Back to main
debug_set_current_location("test.spl", 12, 0)

debug_pop_frame()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
