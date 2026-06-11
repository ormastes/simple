# Codegen Feature Validation

> Validates code generation concepts including JIT/AOT compilation verification, buffer pool recycling, and generator state machine basics. Tests focus on language-level patterns that exercise these features.

<!-- sdn-diagram:id=codegen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=codegen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

codegen_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=codegen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Codegen Feature Validation

Validates code generation concepts including JIT/AOT compilation verification, buffer pool recycling, and generator state machine basics. Tests focus on language-level patterns that exercise these features.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #100 Cranelift Backend, #95 Buffer Pool, #96 Generator Codegen |
| Category | Codegen |
| Status | Complete |
| Source | `test/01_unit/lib/common/feature_validation/codegen_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates code generation concepts including JIT/AOT compilation verification,
buffer pool recycling, and generator state machine basics. Tests focus on
language-level patterns that exercise these features.

## Scenarios

### Feature #100 - Cranelift Backend

#### integer operations

#### compiles integer arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 20
val sum = a + b
expect(sum).to_equal(30)
```

</details>

#### compiles multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 7
val y = 6
expect(x * y).to_equal(42)
```

</details>

#### compiles division

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dividend = 100
val divisor = 4
expect(dividend / divisor).to_equal(25)
```

</details>

#### compiles modulo

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(17 % 5).to_equal(2)
```

</details>

#### compiles negative numbers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val neg = -42
expect(neg + 42).to_equal(0)
```

</details>

#### comparison operations

#### compiles equality comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1 == 1).to_equal(true)
expect(1 == 2).to_equal(false)
```

</details>

#### compiles ordering comparisons

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(1 < 2).to_equal(true)
expect(2 > 1).to_equal(true)
expect(5 <= 5).to_equal(true)
expect(5 >= 5).to_equal(true)
```

</details>

#### function calls

#### compiles simple function

1. fn add
   - Expected: add(3, 4) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a, b):
    a + b
expect(add(3, 4)).to_equal(7)
```

</details>

#### compiles recursive function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(factorial(5)).to_equal(120)
```

</details>

#### compiles nested function calls

1. fn double
2. fn add one
   - Expected: add_one(double(5)) equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x):
    x * 2
fn add_one(x):
    x + 1
expect(add_one(double(5))).to_equal(11)
```

</details>

#### control flow

#### compiles if/else expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val result = if x > 5: "big" else: "small"
expect(result).to_equal("big")
```

</details>

<details>
<summary>Advanced: compiles while loop</summary>

#### compiles while loop

1. fn while sum
   - Expected: while_sum() equals `55`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn while_sum() -> i64:
    var sum = 0
    var i = 1
    while i <= 10:
        sum = sum + i
        i = i + 1
    sum
expect(while_sum()).to_equal(55)
```

</details>


</details>

<details>
<summary>Advanced: compiles for loop</summary>

#### compiles for loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var total = 0
for n in [1, 2, 3, 4, 5]:
    total = total + n
expect(total).to_equal(15)
```

</details>


</details>

#### string operations

#### compiles string creation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect(s).to_equal("hello")
```

</details>

#### compiles string interpolation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 42
val s = "value is {n}"
expect(s).to_equal("value is 42")
```

</details>

#### compiles string concatenation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = "foo"
val b = "bar"
expect(a + b).to_equal("foobar")
```

</details>

#### collection operations

#### compiles array creation and access

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
expect(arr[0]).to_equal(10)
expect(arr[2]).to_equal(30)
```

</details>

#### compiles array length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
expect(arr.len()).to_equal(5)
```

</details>

### Feature #95 - Buffer Pool Concepts

#### collection reuse pattern

#### demonstrates array recycling pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Buffer pool concept: reuse allocations
var buffer = []
# Fill buffer
for i in [1, 2, 3, 4, 5]:
    buffer = buffer + [i]
expect(buffer.len()).to_equal(5)

# Reset and reuse (simulates pool recycling)
buffer = []
for i in [10, 20, 30]:
    buffer = buffer + [i]
expect(buffer.len()).to_equal(3)
expect(buffer[0]).to_equal(10)
```

</details>

#### handles multiple buffer instances

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf1 = []
var buf2 = []

buf1 = buf1 + [1, 2, 3]
buf2 = buf2 + [4, 5, 6]

expect(buf1.len()).to_equal(3)
expect(buf2.len()).to_equal(3)
expect(buf1[0]).to_equal(1)
expect(buf2[0]).to_equal(4)
```

</details>

#### validates buffer capacity growth

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buffer = []
for i in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]:
    buffer = buffer + [i]
expect(buffer.len()).to_equal(10)
expect(buffer[9]).to_equal(10)
```

</details>

#### string buffer patterns

#### builds strings incrementally

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = ""
for word in ["hello", " ", "world"]:
    result = result + word
expect(result).to_equal("hello world")
```

</details>

#### reuses string buffer

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var buf = ""
buf = buf + "line1\n"
buf = buf + "line2\n"
expect(buf).to_contain("line1")
expect(buf).to_contain("line2")
```

</details>

### Feature #96 - Generator State Machine Concepts

#### state machine pattern

#### simulates basic state machine

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulates a generator state machine with explicit state
var state = 0
var values = []

# Step 1
if state == 0:
    values = values + [1]
    state = 1

# Step 2
if state == 1:
    values = values + [2]
    state = 2

# Step 3
if state == 2:
    values = values + [3]
    state = 3

expect(values).to_equal([1, 2, 3])
expect(state).to_equal(3)
```

</details>

#### simulates state machine with transitions

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var state = "idle"
var output = []

# Transition: idle -> running
if state == "idle":
    state = "running"
    output = output + ["started"]

# Transition: running -> paused
if state == "running":
    state = "paused"
    output = output + ["paused"]

# Transition: paused -> running
if state == "paused":
    state = "running"
    output = output + ["resumed"]

expect(output.len()).to_equal(3)
expect(output[0]).to_equal("started")
expect(state).to_equal("running")
```

</details>

#### iterator-like patterns

#### generates sequence of values

1. fn gen sequence
   - Expected: generated equals `[0, 1, 2, 3, 4]`
   - Expected: generated.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Simulates a range generator
fn gen_sequence() -> [i64]:
    var current = 0
    val max_val = 5
    var generated = []
    while current < max_val:
        generated = generated + [current]
        current = current + 1
    generated
val generated = gen_sequence()
expect(generated).to_equal([0, 1, 2, 3, 4])
expect(generated.len()).to_equal(5)
```

</details>

#### generates fibonacci-like sequence

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = 0
var b = 1
var sequence = [a, b]

for i in [0, 1, 2, 3, 4]:
    val next = a + b
    sequence = sequence + [next]
    a = b
    b = next

expect(sequence[0]).to_equal(0)
expect(sequence[1]).to_equal(1)
expect(sequence[2]).to_equal(1)
expect(sequence[3]).to_equal(2)
expect(sequence[4]).to_equal(3)
expect(sequence[5]).to_equal(5)
expect(sequence[6]).to_equal(8)
```

</details>

#### generates values with accumulator

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
var partial_sums = []

for n in [1, 2, 3, 4, 5]:
    sum = sum + n
    partial_sums = partial_sums + [sum]

expect(partial_sums).to_equal([1, 3, 6, 10, 15])
```

</details>

#### dispatcher entry pattern

#### dispatches based on state index

1. fn dispatch
   - Expected: dispatch(0) equals `init`
   - Expected: dispatch(1) equals `process`
   - Expected: dispatch(2) equals `finalize`
   - Expected: dispatch(3) equals `done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn dispatch(state):
    if state == 0:
        return "init"
    elif state == 1:
        return "process"
    elif state == 2:
        return "finalize"
    else:
        return "done"

expect(dispatch(0)).to_equal("init")
expect(dispatch(1)).to_equal("process")
expect(dispatch(2)).to_equal("finalize")
expect(dispatch(3)).to_equal("done")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
