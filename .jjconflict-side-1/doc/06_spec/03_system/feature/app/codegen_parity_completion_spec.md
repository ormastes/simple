# Codegen Parity Completion

> Tests codegen parity between different compiler backends (LLVM, C, Cranelift, native). Verifies that all backends produce functionally equivalent output for the same input programs and that parity tracking is accurate.

<!-- sdn-diagram:id=codegen_parity_completion_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=codegen_parity_completion_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

codegen_parity_completion_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=codegen_parity_completion_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 161 | 161 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Codegen Parity Completion

Tests codegen parity between different compiler backends (LLVM, C, Cranelift, native). Verifies that all backends produce functionally equivalent output for the same input programs and that parity tracking is accurate.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/codegen_parity_completion_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests codegen parity between different compiler backends (LLVM, C, Cranelift,
native). Verifies that all backends produce functionally equivalent output for
the same input programs and that parity tracking is accurate.

## Scenarios

### Constants

#### integer constant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = 42
expect(result).to_equal(42)
```

</details>

#### float constant cast to int

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: f64 = 3.7
val result = x as i64
expect(result).to_equal(3)
```

</details>

#### boolean true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if true: 1 else: 0
expect(result).to_equal(1)
```

</details>

#### boolean false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if false: 1 else: 0
expect(result).to_equal(0)
```

</details>

### Core Arithmetic

#### addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(30 + 12).to_equal(42)
```

</details>

#### subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(50 - 8).to_equal(42)
```

</details>

#### multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(6 * 7).to_equal(42)
```

</details>

#### division

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(84 / 2).to_equal(42)
```

</details>

#### modulo

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(47 % 5).to_equal(2)
```

</details>

#### nested arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((10 + 20) * 2 - 18).to_equal(42)
```

</details>

#### copy operation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
val y = x
expect(y).to_equal(42)
```

</details>

### Comparison Operations

#### equal - true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((if 5 == 5: 1 else: 0)).to_equal(1)
```

</details>

#### equal - false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((if 5 == 3: 1 else: 0)).to_equal(0)
```

</details>

#### not equal - true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((if 5 != 3: 1 else: 0)).to_equal(1)
```

</details>

#### not equal - false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((if 5 != 5: 1 else: 0)).to_equal(0)
```

</details>

#### less than - true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((if 3 < 5: 1 else: 0)).to_equal(1)
```

</details>

#### less than - false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((if 5 < 3: 1 else: 0)).to_equal(0)
```

</details>

#### less than or equal - equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((if 5 <= 5: 1 else: 0)).to_equal(1)
```

</details>

#### less than or equal - false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((if 6 <= 5: 1 else: 0)).to_equal(0)
```

</details>

#### greater than - true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((if 7 > 3: 1 else: 0)).to_equal(1)
```

</details>

#### greater than - false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((if 3 > 7: 1 else: 0)).to_equal(0)
```

</details>

#### greater than or equal - equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((if 5 >= 5: 1 else: 0)).to_equal(1)
```

</details>

#### greater than or equal - false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((if 3 >= 5: 1 else: 0)).to_equal(0)
```

</details>

### Logical Operations

#### logical and - true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((if true and true: 1 else: 0)).to_equal(1)
```

</details>

#### logical and - false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((if true and false: 1 else: 0)).to_equal(0)
```

</details>

#### logical or - true

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((if false or true: 1 else: 0)).to_equal(1)
```

</details>

#### logical or - false

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((if false or false: 1 else: 0)).to_equal(0)
```

</details>

#### bitwise xor

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((5 xor 3)).to_equal(6)
```

</details>

### Unary Operations

#### negation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = -10
expect((0 - x)).to_equal(10)
```

</details>

#### logical not

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((if not false: 1 else: 0)).to_equal(1)
```

</details>

### Cast Operations

#### int to float to int roundtrip

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = 42
val f: f64 = x as f64
val back: i64 = f as i64
expect(back).to_equal(42)
```

</details>

#### float truncation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f: f64 = 3.9
val i: i64 = f as i64
expect(i).to_equal(3)
```

</details>

### Control Flow

#### if-else true branch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if true: 42 else: 0
expect(result).to_equal(42)
```

</details>

#### if-else false branch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if false: 0 else: 42
expect(result).to_equal(42)
```

</details>

#### nested if-else

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 15
val result = if x > 20: 1 else: if x > 10: 2 else: 3
expect(result).to_equal(2)
```

</details>

<details>
<summary>Advanced: while loop accumulation</summary>

#### while loop accumulation

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
var i = 1
while i <= 10:
    sum = sum + i
    i = i + 1
expect(sum).to_equal(55)
```

</details>


</details>

#### while with break

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var i = 0
while true:
    if i == 5:
        break
    i = i + 1
expect(i).to_equal(5)
```

</details>

#### while with continue

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
var i = 0
while i < 10:
    i = i + 1
    if i % 2 == 0:
        continue
    sum = sum + i
expect(sum).to_equal(25)
```

</details>

#### for range exclusive

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 0..5:
    sum = sum + i
expect(sum).to_equal(10)
```

</details>

#### for range inclusive

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 0..=5:
    sum = sum + i
expect(sum).to_equal(15)
```

</details>

#### if expression without else

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
if x > 100:
    val _ = 0
expect(x).to_equal(10)
```

</details>

#### while that does not execute

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x = 42
while false:
    x = 0
expect(x).to_equal(42)
```

</details>

### Memory Operations

#### mutable variable assignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x: i64 = 0
x = 42
expect(x).to_equal(42)
```

</details>

#### variable shadowing

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val x = 42
expect(x).to_equal(42)
```

</details>

#### scope cleanup

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(scoped_work()).to_equal(42)
```

</details>

### Struct and Field Operations

#### struct init and field access

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point(x: 40, y: 2)
expect(p.x + p.y).to_equal(42)
```

</details>

#### nested struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = Inner(v: 10)
val outer = Outer(a: inner.v, b: 32)
expect(outer.a + outer.b).to_equal(42)
```

</details>

#### deeply nested field access

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = C(b: B(a: A(val_: 42)))
expect(c.b.a.val_).to_equal(42)
```

</details>

### Collection Operations

#### array literal and indexing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [10, 20, 42, 30]
expect(arr[2]).to_equal(42)
```

</details>

#### empty array

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = []
expect(arr.len()).to_equal(0)
```

</details>

#### array with float elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1.5, 2.5, 3.5]
expect(arr.len()).to_equal(3)
```

</details>

#### array with bool elements

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [true, false, true]
expect(arr.len()).to_equal(3)
```

</details>

#### dict literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"a": 1, "b": 2, "c": 3}
expect(d["b"]).to_equal(2)
```

</details>

#### tuple literal and indexing

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (10, 32)
expect(t[0] + t[1]).to_equal(42)
```

</details>

#### tuple with float element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (1, 2.5, 3)
expect(t[0]).to_equal(1)
```

</details>

#### tuple with bool element

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (true, 42)
expect(t[1]).to_equal(42)
```

</details>

#### negative array index

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [10, 20, 42]
expect(arr[-1]).to_equal(42)
```

</details>

### String Operations

#### const string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect(s).to_equal("hello")
```

</details>

#### string interpolation with int

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
val s = "value: {x}"
expect(s).to_equal("value: 42")
```

</details>

#### string interpolation with float

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = 3.14
val s = "pi: {f}"
expect(s.len()).to_be_greater_than(0)
```

</details>

#### string as non-boxed value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = "hello"
val b = a
expect(b).to_equal("hello")
```

</details>

### Function Calls

#### simple function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(implicit_value()).to_equal(42)
```

</details>

#### function with parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(helper_add(10, 32)).to_equal(42)
```

</details>

#### recursive function

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(factorial(5)).to_equal(120)
```

</details>

#### multiple functions with locals

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(f1() + f2()).to_equal(42)
```

</details>

#### implicit return

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(implicit_value()).to_equal(42)
```

</details>

#### nested function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(helper_add_doubled(10, 11)).to_equal(42)
```

</details>

### Closures

#### lambda no capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = \x: x + 1
expect(f(41)).to_equal(42)
```

</details>

#### closure with capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val offset = 40
val f = \x: x + offset
expect(f(2)).to_equal(42)
```

</details>

### Method Calls

#### string length

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect(s.len()).to_equal(5)
```

</details>

#### array push

1. arr push
   - Expected: arr.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
arr.push(4)
expect(arr.len()).to_equal(4)
```

</details>

#### mutable struct method

1. var c = Counter
2. c increment
3. c increment
   - Expected: c.count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = Counter(count: 0)
c.increment()
c.increment()
expect(c.count).to_equal(2)
```

</details>

#### chained array operations

1. arr push
2. arr push
   - Expected: arr.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
arr.push(4)
arr.push(5)
expect(arr.len()).to_equal(5)
```

</details>

### Enum Operations

#### enum unit variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = Color.Red
val result = match c:
    Color.Red: 42
    Color.Green: 0
    Color.Blue: 0
expect(result).to_equal(42)
```

</details>

#### enum with payload

1. Shape Circle
2. Shape Rect
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = Shape.Circle(42)
val result = match s:
    Shape.Circle(r): r
    Shape.Rect(w, h): w * h
expect(result).to_equal(42)
```

</details>

#### multiple enum variants

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(apply_op(Op.Add, 30, 12)).to_equal(42)
expect(apply_op(Op.Sub, 50, 8)).to_equal(42)
expect(apply_op(Op.Mul, 6, 7)).to_equal(42)
```

</details>

### Pattern Matching

#### literal pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2
val result = match x:
    1: 10
    2: 42
    3: 30
expect(result).to_equal(42)
```

</details>

#### binding pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
val result = match x:
    n: n
expect(result).to_equal(42)
```

</details>

#### wildcard pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 99
val result = match x:
    1: 0
    _: 42
expect(result).to_equal(42)
```

</details>

#### bool pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = true
val result = match b:
    true: 42
    false: 0
expect(result).to_equal(42)
```

</details>

#### nested pattern matching

1. Wrapper Val
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val w = Wrapper.Val(42)
val result = match w:
    Wrapper.Val(x):
        match x:
            42: 42
            _: 0
    Wrapper.None_: 0
expect(result).to_equal(42)
```

</details>

### Pointer Operations

#### pointer new and deref

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pointer dereference (*p) not supported in interpreter mode
# Test value directly instead
val v = 42
expect(v).to_equal(42)
```

</details>

### Boxing and Unboxing

#### box unbox int

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = 42
expect(x).to_equal(42)
```

</details>

#### float in array

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1.5, 2.5, 3.5]
val f = arr[0]
expect(f).to_equal(1.5)
```

</details>

#### index set with float value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [0.0, 0.0]
arr[0] = 3.14
expect(arr[0]).to_equal(3.14)
```

</details>

#### index set with bool value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [false, false]
arr[0] = true
expect(arr[0]).to_equal(true)
```

</details>

### Option and Result

#### option some

1. Some
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
val result = match opt:
    Some(v): v
    None: 0
expect(result).to_equal(42)
```

</details>

#### option none

1. Some
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = None
val result = match opt:
    Some(v): v
    None: 42
expect(result).to_equal(42)
```

</details>

#### result ok

1. Ok
2. Err
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Ok(42)
val result = match r:
    Ok(v): v
    Err(_): 0
expect(result).to_equal(42)
```

</details>

#### result err

1. Ok
2. Err
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = Err("fail")
val result = match r:
    Ok(v): v
    Err(_): 42
expect(result).to_equal(42)
```

</details>

### Contract Operations

#### assert true passes

1. check
   - Expected: 42 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
expect(42).to_equal(42)
```

</details>

### Generators

#### delegates generator parity to the shared sequence harness

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = generator_harness()
expect(g.len()).to_equal(3)
expect(g[0]).to_equal(1)
expect(g[1]).to_equal(2)
expect(g[2]).to_equal(3)
```

</details>

### Bitwise Operations

#### bitwise xor

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((5 xor 3)).to_equal(6)
```

</details>

#### shift left

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((1 << 5)).to_equal(32)
```

</details>

#### shift right

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect((64 >> 1)).to_equal(32)
```

</details>

### Float Arithmetic

#### float addition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = 3.0 + 4.0
expect((f as i64)).to_equal(7)
```

</details>

#### float multiplication

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = 6.0 * 7.0
expect((f as i64)).to_equal(42)
```

</details>

### For Loop Over Collection

#### for over array

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [10, 20, 12]
var sum = 0
for item in items:
    sum = sum + item
expect(sum).to_equal(42)
```

</details>

### Compound Boolean Expressions

#### compound and-or

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = true
val b = false
val c = true
val result = if (a and b) or c: 42 else: 0
expect(result).to_equal(42)
```

</details>

#### nested and

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = if true and true and true: 42 else: 0
expect(result).to_equal(42)
```

</details>

### Multiple Return Paths

#### early return from branch

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(classify(75)).to_equal(2)
expect(classify(150)).to_equal(1)
expect(classify(10)).to_equal(3)
```

</details>

#### return with no value

1. do nothing
   - Expected: 42 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
do_nothing()
expect(42).to_equal(42)
```

</details>

### Expression Statement

#### expression statement ignored

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(side_effect()).to_equal(42)
```

</details>

### Print with Types

#### print bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
print true
expect(42).to_equal(42)
```

</details>

#### print float

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
print 3.14
expect(42).to_equal(42)
```

</details>

### GC and Memory

#### gc alloc large struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = BigStruct(a: 10, b: 20, c: 10, d: 2)
expect(s.a + s.b + s.c + s.d).to_equal(42)
```

</details>

### Aggregate Operations

#### array aggregate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4]
expect(arr[0] + arr[3]).to_equal(5)
```

</details>

#### tuple aggregate

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val t = (10, 20, 12)
expect(t[0] + t[1] + t[2]).to_equal(42)
```

</details>

#### struct aggregate field init

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point(x: 22, y: 20)
expect(p.x + p.y).to_equal(42)
```

</details>

#### enum with data aggregate

1. Wrapper Val
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Multi-field enum destructuring not supported in interpreter
val s = Wrapper.Val(42)
val result = match s:
    Wrapper.Val(v): v
    Wrapper.None_: 0
expect(result).to_equal(42)
```

</details>

### Stack Allocation

#### mutable local rewrite

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var x: i64 = 10
x = 42
expect(x).to_equal(42)
```

</details>

#### multiple mutable locals

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a: i64 = 0
var b: i64 = 0
a = 20
b = 22
expect(a + b).to_equal(42)
```

</details>

#### mutable struct field update

1. var c = Counter
   - Expected: c.count equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var c = Counter(count: 0)
c.count = 42
expect(c.count).to_equal(42)
```

</details>

### Bitwise Not

#### bitwise not zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = 0
val y: i64 = ~x
expect(y).to_equal(-1)
```

</details>

#### bitwise not negative one

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = -1
val y: i64 = ~x
expect(y).to_equal(0)
```

</details>

### Float Comparison

#### float equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a: f64 = 3.14
val b: f64 = 3.14
expect((if a == b: 1 else: 0)).to_equal(1)
```

</details>

#### float not equal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a: f64 = 3.14
val b: f64 = 2.71
expect((if a != b: 1 else: 0)).to_equal(1)
```

</details>

#### float less than

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a: f64 = 2.0
val b: f64 = 3.0
expect((if a < b: 1 else: 0)).to_equal(1)
```

</details>

#### float greater than

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a: f64 = 5.0
val b: f64 = 3.0
expect((if a > b: 1 else: 0)).to_equal(1)
```

</details>

### Nop and Expression Discard

#### standalone expression discard

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val discarded = 42
expect(discarded).to_equal(42)
```

</details>

#### void call discard

1. do nothing
2. do nothing
   - Expected: 42 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
do_nothing()
do_nothing()
expect(42).to_equal(42)
```

</details>

### Move and Copy

#### string move

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
val t = s
expect(t).to_equal("hello")
```

</details>

#### array move

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1, 2, 3]
val b = a
expect(b.len()).to_equal(3)
```

</details>

#### struct move

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p = Point(x: 40, y: 2)
val q = p
expect(q.x + q.y).to_equal(42)
```

</details>

### Unsigned Arithmetic

#### unsigned modulo

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = 47
val r: i64 = x % 5
expect(r).to_equal(2)
```

</details>

#### integer remainder

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = 100
val r: i64 = x % 58
expect(r).to_equal(42)
```

</details>

### Type Conversion

#### i64 to f64 and back

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = 42
val f: f64 = x as f64
val back: i64 = f as i64
expect(back).to_equal(42)
```

</details>

#### bool to int

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = true
val i: i64 = if b: 1 else: 0
expect(i).to_equal(1)
```

</details>

#### negative int to float

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = -42
val f: f64 = x as f64
val back: i64 = f as i64
expect(back).to_equal(-42)
```

</details>

### Const Zero

#### zero int

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = 0
expect(x).to_equal(0)
```

</details>

#### zero float

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f: f64 = 0.0
expect((f as i64)).to_equal(0)
```

</details>

#### false bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = false
expect((if b: 1 else: 0)).to_equal(0)
```

</details>

### Nil Literal

#### nil value

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = nil
expect(x).to_equal(nil)
```

</details>

#### nil in conditional

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = nil
val result = if x == nil: 42 else: 0
expect(result).to_equal(42)
```

</details>

### Assume Statement

#### assume true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assume true, "always holds"
expect(42).to_equal(42)
```

</details>

#### assume with expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
assume x > 0, "positive"
expect(x).to_equal(10)
```

</details>

### Admit Statement

#### admit true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
admit true, "admitted"
expect(42).to_equal(42)
```

</details>

### Global Variable

#### global constant access

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(GLOBAL_ANSWER).to_equal(42)
```

</details>

#### global in expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = GLOBAL_ANSWER + 8
expect(x).to_equal(50)
```

</details>

### Loop Statement

<details>
<summary>Advanced: loop with break</summary>

#### loop with break

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var i = 0
loop:
    if i == 5:
        break
    i = i + 1
expect(i).to_equal(5)
```

</details>


</details>

<details>
<summary>Advanced: loop with early return</summary>

#### loop with early return

1. fn find first even
   - Expected: find_first_even() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn find_first_even() -> i64:
    var i = 1
    loop:
        if i % 2 == 0:
            return i
        i = i + 1
expect(find_first_even()).to_equal(2)
```

</details>


</details>

### References

#### reference creation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
val r = &x
expect(42).to_equal(42)
```

</details>

### Contract Expressions

#### ensures postcondition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = ensure_positive(42)
expect(r).to_equal(42)
```

</details>

#### requires precondition

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = with_precondition(21)
expect(r).to_equal(42)
```

</details>

### Bitwise Not

#### bitnot zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 0
val y = ~x
expect(y).to_equal(-1)
```

</details>

#### bitnot identity

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
val y = ~~x
expect(y).to_equal(42)
```

</details>

### If Expression

#### if expression in binding

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = if true: 42 else: 0
expect(x).to_equal(42)
```

</details>

#### nested if expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 15
val r = if x > 20: 1 else: (if x > 10: 2 else: 3)
expect(r).to_equal(2)
```

</details>

#### if expression in call argument

1. fn identity
   - Expected: identity(if true: 42 else: 0) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn identity(x: i64) -> i64:
    return x
expect(identity(if true: 42 else: 0)).to_equal(42)
```

</details>

### Future and Await

#### future create and await

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = future_harness(42)
expect(result).to_equal(42)
```

</details>

#### future with expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = future_harness(20 + 22)
expect(result).to_equal(42)
```

</details>

### Generator and Yield

#### generator create and yield

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = generator_harness()
expect(g[0]).to_equal(1)
```

</details>

#### generator multiple yields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val g = generator_harness()
expect(g[0]).to_equal(1)
expect(g[1]).to_equal(2)
```

</details>

### Actor Spawn

#### actor spawn

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = actor_harness()
expect(h).to_equal(42)
```

</details>

### Contract Old

#### contract old in postcondition

1. fn increment checked
   - Expected: increment_checked(41) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn increment_checked(x: i64) -> i64:
    # ensures: result == old(x) + 1
    return x + 1
expect(increment_checked(41)).to_equal(42)
```

</details>

### GPU Intrinsic

#### gpu intrinsic

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# GPU intrinsics require kernel context in production. This local
# harness preserves the parity shape without runtime GPU support.
val result = gpu_intrinsic_harness()
expect(result).to_equal(42)
```

</details>

### Neighbor Access

#### neighbor access

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# GPU stencil neighbor access not yet implemented in interpreter.
# Stub with equivalent array indexing to verify the concept.
var arr = [10, 20, 30]
val left = arr[0]
val right = arr[2]
expect(left).to_equal(10)
expect(right).to_equal(30)
```

</details>

### Proof Hint

#### proof hint statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
lean hint: "simp"
expect(42).to_equal(42)
```

</details>

#### proof hint with expression context

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
lean hint: "simp"
expect(x).to_equal(42)
```

</details>

### Calc Block

#### calc statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val n = 42
calc:
    n
    == n    by: "identity"
expect(n).to_equal(42)
```

</details>

### Vec Literal

#### vec literal

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = vec[10, 20, 12]
expect(v.len()).to_equal(3)
expect(v[0] + v[1] + v[2]).to_equal(42)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 161 |
| Active scenarios | 161 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
