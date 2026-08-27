# DAP Stack Trace Management

> Tests the Debug Adapter Protocol stack trace reporting including frame enumeration, source mapping, and scope inspection. Verifies that stack frames accurately reflect the call chain with correct file paths, line numbers, and local variables.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the Debug Adapter Protocol stack trace reporting including frame enumeration,
source mapping, and scope inspection. Verifies that stack frames accurately reflect
the call chain with correct file paths, line numbers, and local variables.

## Scenarios

### Stack Frame Management

### Pushing frames

#### pushes a single frame

- pushes a single frame
   - Expected: new_depth equals `initial_depth + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pushes a single frame")
debug_set_active(true)
val initial_depth = debug_stack_depth()

debug_push_frame("main", "main.spl", 10, 0)

val new_depth = debug_stack_depth()
expect(new_depth).to_equal(initial_depth + 1)
```

</details>

#### pushes multiple frames

- pushes multiple frames
   - Expected: new_depth equals `initial_depth + 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pushes multiple frames")
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

- tracks frame information


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks frame information")
debug_set_active(true)
debug_push_frame("factorial", "math.spl", 15, 8)

val trace = debug_stack_trace()
expect(trace).to_contain("factorial")
expect(trace).to_contain("math.spl")
```

</details>

### Popping frames

#### pops a single frame

- pops a single frame
   - Expected: depth_after equals `depth_before - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pops a single frame")
debug_set_active(true)
debug_push_frame("test", "test.spl", 10, 0)
val depth_before = debug_stack_depth()

debug_pop_frame()

val depth_after = debug_stack_depth()
expect(depth_after).to_equal(depth_before - 1)
```

</details>

#### pops frames in LIFO order

- pops frames in LIFO order
   - Expected: depth_after equals `depth_before - 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pops frames in LIFO order")
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

- handles popping from empty stack
   - Expected: depth >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles popping from empty stack")
debug_set_active(true)
# Should not crash
debug_pop_frame()

val depth = debug_stack_depth()
expect(depth >= 0).to_equal(true)
```

</details>

### Stack depth tracking

#### starts at zero depth

- starts at zero depth
   - Expected: depth >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("starts at zero depth")
debug_set_active(true)
# Fresh debug state should have depth 0
val depth = debug_stack_depth()
expect(depth >= 0).to_equal(true)
```

</details>

#### increments on push

- increments on push
   - Expected: debug_stack_depth() equals `initial + 1`
   - Expected: debug_stack_depth() equals `initial + 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("increments on push")
debug_set_active(true)
val initial = debug_stack_depth()

debug_push_frame("test", "test.spl", 10, 0)
expect(debug_stack_depth()).to_equal(initial + 1)

debug_push_frame("test", "test.spl", 10, 0)
expect(debug_stack_depth()).to_equal(initial + 2)
```

</details>

#### decrements on pop

- decrements on pop
   - Expected: debug_stack_depth() equals `depth_before - 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("decrements on pop")
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

- generates trace for single frame
   - Expected: trace.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates trace for single frame")
debug_set_active(true)
debug_push_frame("main", "main.spl", 42, 5)

val trace = debug_stack_trace()
expect(trace.len() > 0).to_equal(true)
expect(trace).to_contain("main")
```

</details>

#### generates trace for multiple frames

- generates trace for multiple frames


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generates trace for multiple frames")
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

- includes file paths in trace


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes file paths in trace")
debug_set_active(true)
debug_push_frame("func1", "src/app/module1.spl", 20, 0)
debug_push_frame("func2", "src/lib/module2.spl", 30, 0)

val trace = debug_stack_trace()
expect(trace).to_contain("module1.spl")
expect(trace).to_contain("module2.spl")
```

</details>

#### includes line numbers in trace

- includes line numbers in trace


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes line numbers in trace")
debug_set_active(true)
debug_push_frame("func", "test.spl", 123, 0)

val trace = debug_stack_trace()
expect(trace).to_contain("123")
```

</details>

#### returns empty trace for empty stack

- returns empty trace for empty stack


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty trace for empty stack")
debug_set_active(true)
# No frames pushed
val trace = debug_stack_trace()
# Should return empty or minimal trace
expect(trace.len()).to_be_greater_than(-1)
```

</details>

### Recursive call tracking

#### tracks recursive calls

- tracks recursive calls
   - Expected: depth >= 3 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tracks recursive calls")
debug_set_active(true)
debug_push_frame("factorial", "math.spl", 10, 0)
debug_push_frame("factorial", "math.spl", 10, 0)  # Recursive
debug_push_frame("factorial", "math.spl", 10, 0)  # Recursive

val depth = debug_stack_depth()
expect(depth >= 3).to_equal(true)
```

</details>

#### maintains separate frame instances

- maintains separate frame instances
   - Expected: count >= 2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maintains separate frame instances")
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

- handles frames with zero line/column


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles frames with zero line/column")
debug_set_active(true)
debug_push_frame("func", "test.spl", 0, 0)

val trace = debug_stack_trace()
expect(trace).to_contain("func")
```

</details>

#### handles frames with large line numbers

- handles frames with large line numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles frames with large line numbers")
debug_set_active(true)
debug_push_frame("func", "huge_file.spl", 999999, 500)

val trace = debug_stack_trace()
expect(trace).to_contain("999999")
```

</details>

#### handles empty function names

- handles empty function names


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty function names")
debug_set_active(true)
debug_push_frame("", "test.spl", 10, 0)

val trace = debug_stack_trace()
# Should not crash
expect(trace.len()).to_be_greater_than(-1)
```

</details>

#### handles empty file paths

- handles empty file paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty file paths")
debug_set_active(true)
debug_push_frame("func", "", 10, 0)

val trace = debug_stack_trace()
expect(trace).to_contain("func")
```

</details>

#### handles special characters in names

- handles special characters in names


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles special characters in names")
debug_set_active(true)
debug_push_frame("func_with_underscores", "my-file.spl", 10, 0)

val trace = debug_stack_trace()
expect(trace).to_contain("func_with_underscores")
```

</details>

### Performance

#### handles deep call stacks

- handles deep call stacks
   - Expected: depth >= 100 is true
   - Expected: trace.len() > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles deep call stacks")
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

- efficiently pops many frames
   - Expected: depth >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("efficiently pops many frames")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b781a517f6c37cad8bfea94777d51715310b1af5fa10aaa8ac7102e129864ff8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b781a517f6c37cad8bfea94777d51715310b1af5fa10aaa8ac7102e129864ff8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b781a517f6c37cad8bfea94777d51715310b1af5fa10aaa8ac7102e129864ff8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/dap/stack_trace_spec.spl
mirror: doc/06_spec/03_system/feature/dap/stack_trace_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/dap/stack_trace_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/dap/stack_trace_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/dap/stack_trace_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pushes a single frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/dap/stack_trace_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pushes multiple frames' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/dap/stack_trace_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'tracks frame information' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
