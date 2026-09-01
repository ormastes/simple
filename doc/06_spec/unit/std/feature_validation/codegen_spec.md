# codegen_spec

> As a compiler maintainer, I need the language-level contracts this file is

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# codegen_spec

As a compiler maintainer, I need the language-level contracts this file is

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/std/feature_validation/codegen_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

As a compiler maintainer, I need the language-level contracts this file is
    named for -- integer and comparison ops, direct/recursive/nested calls,
    if-else / while / for control flow, text creation / interpolation /
    concatenation, and array creation / indexing / length -- pinned to a NAMED
    engine, so that a compiled-lane regression cannot pass review behind a
    suite that only ever ran on the interpreter.

## Scenarios

### Feature #100 - Cranelift Backend

#### integer operations

#### compiles integer arithmetic

- compiles integer arithmetic
   - Expected: sum equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles integer arithmetic")
val a = 10
val b = 20
val sum = a + b
expect(sum).to_equal(30)
```

</details>

#### compiles multiplication

- compiles multiplication
   - Expected: x * y equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles multiplication")
val x = 7
val y = 6
expect(x * y).to_equal(42)
```

</details>

#### compiles division

- compiles division
   - Expected: dividend / divisor equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles division")
val dividend = 100
val divisor = 4
expect(dividend / divisor).to_equal(25)
```

</details>

#### compiles modulo

- compiles modulo
   - Expected: 17 % 5 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles modulo")
expect(17 % 5).to_equal(2)
```

</details>

#### compiles negative numbers

- compiles negative numbers
   - Expected: neg + 42 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles negative numbers")
val neg = -42
expect(neg + 42).to_equal(0)
```

</details>

#### comparison operations

#### compiles equality comparison

- compiles equality comparison
   - Expected: 1 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles equality comparison")
expect(1).to_equal(1)
expect(1).to_not_equal(2)
```

</details>

#### compiles ordering comparisons

- compiles ordering comparisons
   - Expected: 1 < 2 is true
   - Expected: 2 > 1 is true
   - Expected: 5 <= 5 is true
   - Expected: 5 >= 5 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles ordering comparisons")
expect(1 < 2).to_equal(true)
expect(2 > 1).to_equal(true)
expect(5 <= 5).to_equal(true)
expect(5 >= 5).to_equal(true)
```

</details>

#### function calls

#### compiles simple function

- compiles simple function
   - Expected: add(3, 4) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles simple function")
fn add(a, b):
    a + b
expect(add(3, 4)).to_equal(7)
```

</details>

#### compiles recursive function

- compiles recursive function
   - Expected: factorial(5) equals `120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles recursive function")
fn factorial(n):
    if n <= 1:
        return 1
    n * factorial(n - 1)
expect(factorial(5)).to_equal(120)
```

</details>

#### compiles nested function calls

- compiles nested function calls
   - Expected: add_one(double(5)) equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles nested function calls")
fn double(x):
    x * 2
fn add_one(x):
    x + 1
expect(add_one(double(5))).to_equal(11)
```

</details>

#### control flow

#### compiles if/else expressions

- compiles if/else expressions
   - Expected: result equals `big`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles if/else expressions")
val x = 10
val result = if x > 5: "big" else: "small"
expect(result).to_equal("big")
```

</details>

<details>
<summary>Advanced: compiles while loop</summary>

#### compiles while loop

- compiles while loop
   - Expected: while_sum() equals `55`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles while loop")
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

- compiles for loop
   - Expected: total equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles for loop")
var total = 0
for n in [1, 2, 3, 4, 5]:
    total = total + n
expect(total).to_equal(15)
```

</details>


</details>

#### string operations

#### compiles string creation

- compiles string creation
   - Expected: s equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles string creation")
val s = "hello"
expect(s).to_equal("hello")
```

</details>

#### compiles string interpolation

- compiles string interpolation
   - Expected: s equals `value is 42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles string interpolation")
val n = 42
val s = "value is {n}"
expect(s).to_equal("value is 42")
```

</details>

#### compiles string concatenation

- compiles string concatenation
   - Expected: a + b equals `foobar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles string concatenation")
val a = "foo"
val b = "bar"
expect(a + b).to_equal("foobar")
```

</details>

#### collection operations

#### compiles array creation and access

- compiles array creation and access
   - Expected: arr[0] equals `10`
   - Expected: arr[2] equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles array creation and access")
val arr = [10, 20, 30]
expect(arr[0]).to_equal(10)
expect(arr[2]).to_equal(30)
```

</details>

#### compiles array length

- compiles array length
   - Expected: arr.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles array length")
val arr = [1, 2, 3, 4, 5]
expect(arr.len()).to_equal(5)
```

</details>

### Feature #95 - Buffer Pool Concepts

#### collection reuse pattern

#### demonstrates array recycling pattern

- demonstrates array recycling pattern
   - Expected: buffer.len() equals `5`
   - Expected: buffer.len() equals `3`
   - Expected: buffer[0] equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("demonstrates array recycling pattern")
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

- handles multiple buffer instances
   - Expected: buf1.len() equals `3`
   - Expected: buf2.len() equals `3`
   - Expected: buf1[0] equals `1`
   - Expected: buf2[0] equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiple buffer instances")
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

- validates buffer capacity growth
   - Expected: buffer.len() equals `10`
   - Expected: buffer[9] equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("validates buffer capacity growth")
var buffer = []
for i in [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]:
    buffer = buffer + [i]
expect(buffer.len()).to_equal(10)
expect(buffer[9]).to_equal(10)
```

</details>

#### string buffer patterns

#### builds strings incrementally

- builds strings incrementally
   - Expected: result equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds strings incrementally")
var result = ""
for word in ["hello", " ", "world"]:
    result = result + word
expect(result).to_equal("hello world")
```

</details>

#### reuses string buffer

- reuses string buffer


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reuses string buffer")
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

- simulates basic state machine
   - Expected: values equals `[1, 2, 3]`
   - Expected: state equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simulates basic state machine")
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

- simulates state machine with transitions
   - Expected: output.len() equals `3`
   - Expected: output[0] equals `started`
   - Expected: state equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("simulates state machine with transitions")
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

- generates sequence of values
   - Expected: generated equals `[0, 1, 2, 3, 4]`
   - Expected: generated.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates sequence of values")
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

- generates fibonacci-like sequence
   - Expected: sequence[0] equals `0`
   - Expected: sequence[1] equals `1`
   - Expected: sequence[2] equals `1`
   - Expected: sequence[3] equals `2`
   - Expected: sequence[4] equals `3`
   - Expected: sequence[5] equals `5`
   - Expected: sequence[6] equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates fibonacci-like sequence")
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

- generates values with accumulator
   - Expected: partial_sums equals `[1, 3, 6, 10, 15]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates values with accumulator")
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

- dispatches based on state index
   - Expected: dispatch(0) equals `init`
   - Expected: dispatch(1) equals `process`
   - Expected: dispatch(2) equals `finalize`
   - Expected: dispatch(3) equals `done`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dispatches based on state index")
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

### Feature #100 - Cranelift Backend holds under the JIT lane (out of process)

#### passes the probe under the interpreter

- passes the probe under the interpreter


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes the probe under the interpreter")
# Control column. The interpreter is the engine the examples above
# already exercise, so this arm failing means the probe or the harness
# broke, not codegen.
expect(engine_stdout(_CODEGEN_PROBE, "interpret")).to_contain(_CODEGEN_PASS)
```

</details>

#### passes the probe under the cranelift JIT

- passes the probe under the cranelift JIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes the probe under the cranelift JIT")
# The arm that carries the weight: the same 50 checks, compiled.
expect(engine_stdout(_CODEGEN_PROBE, "jit")).to_contain(_CODEGEN_PASS)
```

</details>

#### proves each arm reached the engine it names

- proves each arm reached the engine it names


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("proves each arm reached the engine it names")
# A probe printing the same verdict on both engines cannot by itself
# prove the "jit" arm reached the JIT: one unsupported operation
# silently demotes a whole program back to the interpreter, and an
# unrecognised SIMPLE_EXECUTION_MODE value silently selects the JIT.
# The probe therefore also reports a live, still-OPEN divergence --
# `Dict<text, f64>.get()` on a miss, which the F64 decode arm
# deliberately does not guard (expr_dispatch.spl:991).
#
# Measured 2026-08-09, same probe, same binary, both engines:
#   interpret -> PROBE ENGINE CANARY: true    (correct)
#   jit       -> PROBE ENGINE CANARY: false   (the open gap)
expect(engine_stdout(_CODEGEN_PROBE, "interpret")).to_contain("PROBE ENGINE CANARY: true")
expect(engine_stdout(_CODEGEN_PROBE, "jit")).to_contain("PROBE ENGINE CANARY: false")
```

</details>

#### rejects an unrecognised engine name instead of silently using the JIT

- rejects an unrecognised engine name instead of silently using the JIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an unrecognised engine name instead of silently using the JIT")
assert_false(is_known_engine("interp"))
assert_false(is_known_engine("native"))
assert_true(is_known_engine("jit"))
assert_true(is_known_engine("interpret"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
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

- Canonical SPipe generation for source `e1184f820d3062974d15a1df336b7ff3ddd225a5b4ea6e1c731ec7c01111728e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e1184f820d3062974d15a1df336b7ff3ddd225a5b4ea6e1c731ec7c01111728e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e1184f820d3062974d15a1df336b7ff3ddd225a5b4ea6e1c731ec7c01111728e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/std/feature_validation/codegen_spec.spl
mirror: doc/06_spec/unit/std/feature_validation/codegen_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/std/feature_validation/codegen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/std/feature_validation/codegen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/std/feature_validation/codegen_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 33 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/std/feature_validation/codegen_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles integer arithmetic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/std/feature_validation/codegen_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles multiplication' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/std/feature_validation/codegen_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles division' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
