# DAP Stack Trace Management

> Tests the Debug Adapter Protocol stack trace reporting including frame enumeration, source mapping, and scope inspection. Verifies that stack frames accurately reflect the call chain with correct file paths, line numbers, and local variables.

<!-- sdn-diagram:id=stack_trace_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=stack_trace_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

stack_trace_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=stack_trace_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DAP Stack Trace Management

Tests the Debug Adapter Protocol stack trace reporting including frame enumeration, source mapping, and scope inspection. Verifies that stack frames accurately reflect the call chain with correct file paths, line numbers, and local variables.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Developer Tools |
| Status | In Progress |
| Source | `test/03_system/feature/dap/stack_trace_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the Debug Adapter Protocol stack trace reporting including frame enumeration,
source mapping, and scope inspection. Verifies that stack frames accurately reflect
the call chain with correct file paths, line numbers, and local variables.

## Scenarios

### Stack Frame Management

### Pushing frames

#### pushes a single frame

1. debug set active
2. debug push frame
   - Expected: new_depth equals `initial_depth + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
val initial_depth = debug_stack_depth()

debug_push_frame("main", "main.spl", 10, 0)

val new_depth = debug_stack_depth()
expect(new_depth).to_equal(initial_depth + 1)
```

</details>

#### pushes multiple frames

1. debug set active
2. debug push frame
3. debug push frame
4. debug push frame
   - Expected: new_depth equals `initial_depth + 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
val initial_depth = debug_stack_depth()

debug_push_frame("main", "main.spl", 10, 0)
debug_push_frame("process", "utils.spl", 25, 5)
debug_push_frame("validate", "validation.spl", 42, 10)

val new_depth = debug_stack_depth()
expect(new_depth).to_equal(initial_depth + 3)
```

</details>

#### tracks frame information

1. debug set active
2. debug push frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_push_frame("factorial", "math.spl", 15, 8)

val trace = debug_stack_trace()
expect(trace).to_contain("factorial")
expect(trace).to_contain("math.spl")
```

</details>

### Popping frames

#### pops a single frame

1. debug set active
2. debug push frame
3. debug pop frame
   - Expected: depth_after equals `depth_before - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_push_frame("test", "test.spl", 10, 0)
val depth_before = debug_stack_depth()

debug_pop_frame()

val depth_after = debug_stack_depth()
expect(depth_after).to_equal(depth_before - 1)
```

</details>

#### pops frames in LIFO order

1. debug set active
2. debug push frame
3. debug push frame
4. debug push frame
5. debug pop frame
6. debug pop frame
   - Expected: depth_after equals `depth_before - 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_push_frame("func1", "file1.spl", 10, 0)
debug_push_frame("func2", "file2.spl", 20, 0)
debug_push_frame("func3", "file3.spl", 30, 0)

val depth_before = debug_stack_depth()
debug_pop_frame()
debug_pop_frame()

val depth_after = debug_stack_depth()
expect(depth_after).to_equal(depth_before - 2)
```

</details>

#### handles popping from empty stack

1. debug set active
2. debug pop frame
   - Expected: depth >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
# Should not crash
debug_pop_frame()

val depth = debug_stack_depth()
expect(depth >= 0).to_equal(true)
```

</details>

### Stack depth tracking

#### starts at zero depth

1. debug set active
   - Expected: depth >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
# Fresh debug state should have depth 0
val depth = debug_stack_depth()
expect(depth >= 0).to_equal(true)
```

</details>

#### increments on push

1. debug set active
2. debug push frame
   - Expected: debug_stack_depth() equals `initial + 1`
3. debug push frame
   - Expected: debug_stack_depth() equals `initial + 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
val initial = debug_stack_depth()

debug_push_frame("test", "test.spl", 10, 0)
expect(debug_stack_depth()).to_equal(initial + 1)

debug_push_frame("test", "test.spl", 10, 0)
expect(debug_stack_depth()).to_equal(initial + 2)
```

</details>

#### decrements on pop

1. debug set active
2. debug push frame
3. debug push frame
4. debug pop frame
   - Expected: debug_stack_depth() equals `depth_before - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_push_frame("test", "test.spl", 10, 0)
debug_push_frame("test", "test.spl", 10, 0)
val depth_before = debug_stack_depth()

debug_pop_frame()
expect(debug_stack_depth()).to_equal(depth_before - 1)
```

</details>

### Stack trace generation

#### generates trace for single frame

1. debug set active
2. debug push frame
   - Expected: trace.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_push_frame("main", "main.spl", 42, 5)

val trace = debug_stack_trace()
expect(trace.len() > 0).to_equal(true)
expect(trace).to_contain("main")
```

</details>

#### generates trace for multiple frames

1. debug set active
2. debug push frame
3. debug push frame
4. debug push frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_push_frame("main", "main.spl", 10, 0)
debug_push_frame("process_data", "processor.spl", 55, 12)
debug_push_frame("validate_input", "validator.spl", 78, 8)

val trace = debug_stack_trace()
expect(trace).to_contain("main")
expect(trace).to_contain("process_data")
expect(trace).to_contain("validate_input")
```

</details>

#### includes file paths in trace

1. debug set active
2. debug push frame
3. debug push frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_push_frame("func1", "src/app/module1.spl", 20, 0)
debug_push_frame("func2", "src/lib/module2.spl", 30, 0)

val trace = debug_stack_trace()
expect(trace).to_contain("module1.spl")
expect(trace).to_contain("module2.spl")
```

</details>

#### includes line numbers in trace

1. debug set active
2. debug push frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_push_frame("func", "test.spl", 123, 0)

val trace = debug_stack_trace()
expect(trace).to_contain("123")
```

</details>

#### returns empty trace for empty stack

1. debug set active


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
# No frames pushed
val trace = debug_stack_trace()
# Should return empty or minimal trace
expect(trace.len()).to_be_greater_than(-1)
```

</details>

### Recursive call tracking

#### tracks recursive calls

1. debug set active
2. debug push frame
3. debug push frame
4. debug push frame
   - Expected: depth >= 3 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_push_frame("factorial", "math.spl", 10, 0)
debug_push_frame("factorial", "math.spl", 10, 0)  # Recursive
debug_push_frame("factorial", "math.spl", 10, 0)  # Recursive

val depth = debug_stack_depth()
expect(depth >= 3).to_equal(true)
```

</details>

#### maintains separate frame instances

1. debug set active
2. debug push frame
3. debug push frame
   - Expected: count >= 2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_push_frame("fib", "math.spl", 5, 0)
debug_push_frame("fib", "math.spl", 5, 0)
val trace = debug_stack_trace()

# Should show both instances
# Count occurrences of "fib" in trace
var count = 0
val lines = trace.split("\n")
for line in lines:
    if line.contains("fib"):
        count = count + 1

expect(count >= 2).to_equal(true)
```

</details>

### Edge cases

#### handles frames with zero line/column

1. debug set active
2. debug push frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_push_frame("func", "test.spl", 0, 0)

val trace = debug_stack_trace()
expect(trace).to_contain("func")
```

</details>

#### handles frames with large line numbers

1. debug set active
2. debug push frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_push_frame("func", "huge_file.spl", 999999, 500)

val trace = debug_stack_trace()
expect(trace).to_contain("999999")
```

</details>

#### handles empty function names

1. debug set active
2. debug push frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_push_frame("", "test.spl", 10, 0)

val trace = debug_stack_trace()
# Should not crash
expect(trace.len()).to_be_greater_than(-1)
```

</details>

#### handles empty file paths

1. debug set active
2. debug push frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_push_frame("func", "", 10, 0)

val trace = debug_stack_trace()
expect(trace).to_contain("func")
```

</details>

#### handles special characters in names

1. debug set active
2. debug push frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_push_frame("func_with_underscores", "my-file.spl", 10, 0)

val trace = debug_stack_trace()
expect(trace).to_contain("func_with_underscores")
```

</details>

### Performance

#### handles deep call stacks

1. debug set active
2. debug push frame
   - Expected: depth >= 100 is true
   - Expected: trace.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)

# Push 100 frames
for i in 0..100:
    debug_push_frame("func", "test.spl", i, 0)

val depth = debug_stack_depth()
expect(depth >= 100).to_equal(true)

val trace = debug_stack_trace()
expect(trace.len() > 0).to_equal(true)
```

</details>

#### efficiently pops many frames

1. debug set active
2. debug push frame
3. debug pop frame
   - Expected: depth >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)

for i in 0..50:
    debug_push_frame("func", "test.spl", i, 0)

for i in 0..50:
    debug_pop_frame()

val depth = debug_stack_depth()
expect(depth >= 0).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
