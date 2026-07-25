# Frame Inspector Specification

> <details>

<!-- sdn-diagram:id=frame_inspector_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=frame_inspector_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

frame_inspector_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=frame_inspector_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Frame Inspector Specification

## Scenarios

### FrameDetail

### construction with of()

#### creates a frame with index, function, file, and line

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = FrameDetail.of(0, "main", "main.spl", 10)
expect(frame.index).to_equal(0)
expect(frame.function_name).to_equal("main")
expect(frame.file).to_equal("main.spl")
expect(frame.line).to_equal(10)
```

</details>

#### sets address to 0 by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = FrameDetail.of(0, "main", "main.spl", 10)
expect(frame.address).to_equal(0)
```

</details>

#### sets full_path to empty by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = FrameDetail.of(0, "main", "main.spl", 10)
expect(frame.full_path).to_equal("")
```

</details>

### construction with full()

#### creates a frame with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = FrameDetail.full(2, "process", "worker.spl", 55, 4096, "/home/user/worker.spl")
expect(frame.index).to_equal(2)
expect(frame.function_name).to_equal("process")
expect(frame.file).to_equal("worker.spl")
expect(frame.line).to_equal(55)
expect(frame.address).to_equal(4096)
expect(frame.full_path).to_equal("/home/user/worker.spl")
```

</details>

#### creates a frame with address 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = FrameDetail.full(0, "main", "main.spl", 1, 0, "/main.spl")
expect(frame.address).to_equal(0)
```

</details>

### to_string()

#### formats frame without address when address is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = FrameDetail.of(0, "main", "main.spl", 10)
val s = frame.to_string()
expect(s).to_equal("#0 main at main.spl:10")
```

</details>

#### formats frame with address when address > 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = FrameDetail.full(1, "helper", "util.spl", 25, 8192, "")
val s = frame.to_string()
expect(s).to_contain("#1 helper at util.spl:25")
expect(s).to_contain("(0x")
```

</details>

#### includes frame index in output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = FrameDetail.of(3, "deep_call", "deep.spl", 99)
val s = frame.to_string()
expect(s).to_start_with("#3")
```

</details>

#### includes function name in output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = FrameDetail.of(0, "my_function", "test.spl", 1)
val s = frame.to_string()
expect(s).to_contain("my_function")
```

</details>

### serialize()

#### serializes with pipe delimiters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = FrameDetail.of(0, "main", "main.spl", 10)
val s = frame.serialize()
expect(s).to_equal("0|main|main.spl|10|0|")
```

</details>

#### serializes full frame with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = FrameDetail.full(2, "process", "worker.spl", 55, 4096, "/home/user/worker.spl")
val s = frame.serialize()
expect(s).to_equal("2|process|worker.spl|55|4096|/home/user/worker.spl")
```

</details>

#### serializes frame with empty file

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = FrameDetail.of(0, "unknown", "", 0)
val s = frame.serialize()
expect(s).to_equal("0|unknown||0|0|")
```

</details>

#### preserves all field values in serialization

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = FrameDetail.full(5, "deep", "nested.spl", 200, 65536, "/abs/nested.spl")
val s = frame.serialize()
expect(s).to_contain("5|")
expect(s).to_contain("|deep|")
expect(s).to_contain("|nested.spl|")
expect(s).to_contain("|200|")
expect(s).to_contain("|65536|")
expect(s).to_end_with("/abs/nested.spl")
```

</details>

### VariableDetail

### construction with of()

#### creates a local variable detail

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = VariableDetail.of("count", "42", "i64")
expect(v.name).to_equal("count")
expect(v.value).to_equal("42")
expect(v.var_type).to_equal("i64")
```

</details>

#### sets num_children to 0 by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = VariableDetail.of("x", "10", "i64")
expect(v.num_children).to_equal(0)
```

</details>

#### sets is_argument to false by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = VariableDetail.of("x", "10", "i64")
expect(v.is_argument).to_equal(false)
```

</details>

### construction with arg()

#### creates an argument variable detail

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = VariableDetail.arg("param", "hello", "text")
expect(v.name).to_equal("param")
expect(v.value).to_equal("hello")
expect(v.var_type).to_equal("text")
```

</details>

#### sets is_argument to true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = VariableDetail.arg("n", "5", "i64")
expect(v.is_argument).to_equal(true)
```

</details>

#### sets num_children to 0 by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = VariableDetail.arg("data", "{}", "struct")
expect(v.num_children).to_equal(0)
```

</details>

### to_string()

#### formats local variable with type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = VariableDetail.of("count", "42", "i64")
val s = v.to_string()
expect(s).to_equal("count = 42 : i64")
```

</details>

#### formats variable without type when type is empty

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = VariableDetail.of("x", "10", "")
val s = v.to_string()
expect(s).to_equal("x = 10")
```

</details>

#### formats argument variable with [arg] marker

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = VariableDetail.arg("param", "hello", "text")
val s = v.to_string()
expect(s).to_equal("param = hello : text [arg]")
```

</details>

#### formats argument without type but with [arg]

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = VariableDetail.arg("n", "5", "")
val s = v.to_string()
expect(s).to_equal("n = 5 [arg]")
```

</details>

#### includes variable name in output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = VariableDetail.of("my_var", "100", "i64")
val s = v.to_string()
expect(s).to_start_with("my_var")
```

</details>

#### includes value in output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = VariableDetail.of("msg", "hello world", "text")
val s = v.to_string()
expect(s).to_contain("hello world")
```

</details>

### serialize()

#### serializes a local variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = VariableDetail.of("count", "42", "i64")
val s = v.serialize()
expect(s).to_equal("count|42|i64|0|0")
```

</details>

#### serializes an argument variable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = VariableDetail.arg("param", "hello", "text")
val s = v.serialize()
expect(s).to_equal("param|hello|text|0|1")
```

</details>

#### serializes variable with empty type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = VariableDetail.of("x", "10", "")
val s = v.serialize()
expect(s).to_equal("x|10||0|0")
```

</details>

#### serializes variable with num_children

1. var v = VariableDetail of
   - Expected: s equals `arr|[1,2,3]|array|3|0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var v = VariableDetail.of("arr", "[1,2,3]", "array")
v.num_children = 3
val s = v.serialize()
expect(s).to_equal("arr|[1,2,3]|array|3|0")
```

</details>

#### preserves argument flag as 1 in serialization

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = VariableDetail.arg("n", "0", "i64")
val s = v.serialize()
expect(s).to_end_with("|1")
```

</details>

#### preserves local flag as 0 in serialization

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = VariableDetail.of("n", "0", "i64")
val s = v.serialize()
expect(s).to_end_with("|0")
```

</details>

### field mutation

#### can modify num_children

1. var v = VariableDetail of
   - Expected: v.num_children equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var v = VariableDetail.of("obj", "{}", "struct")
v.num_children = 5
expect(v.num_children).to_equal(5)
```

</details>

#### can modify value

1. var v = VariableDetail of
   - Expected: v.value equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var v = VariableDetail.of("counter", "0", "i64")
v.value = "10"
expect(v.value).to_equal("10")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/frame_inspector_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FrameDetail
- construction with of()
- construction with full()
- to_string()
- serialize()
- VariableDetail
- construction with of()
- construction with arg()
- to_string()
- serialize()
- field mutation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
