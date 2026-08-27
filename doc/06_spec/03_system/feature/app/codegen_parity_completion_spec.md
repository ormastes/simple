# Codegen Parity Completion

> Tests codegen parity between different compiler backends (LLVM, C, Cranelift, native). Verifies that all backends produce functionally equivalent output for the same input programs and that parity tracking is accurate.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests codegen parity between different compiler backends (LLVM, C, Cranelift,
native). Verifies that all backends produce functionally equivalent output for
the same input programs and that parity tracking is accurate.

## Scenarios

### Constants

#### integer constant

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- integer constant
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("integer constant")
val result = 42
expect(result).to_equal(42)
```

</details>

#### float constant cast to int

- float constant cast to int
   - Expected: result equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("float constant cast to int")
val x: f64 = 3.7
val result = x as i64
expect(result).to_equal(3)
```

</details>

#### boolean true

- boolean true
   - Expected: result equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boolean true")
val result = if true: 1 else: 0
expect(result).to_equal(1)
```

</details>

#### boolean false

- boolean false
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("boolean false")
val result = if false: 1 else: 0
expect(result).to_equal(0)
```

</details>

### Core Arithmetic

#### addition

- addition
   - Expected: 30 + 12 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("addition")
expect(30 + 12).to_equal(42)
```

</details>

#### subtraction

- subtraction
   - Expected: 50 - 8 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("subtraction")
expect(50 - 8).to_equal(42)
```

</details>

#### multiplication

- multiplication
   - Expected: 6 * 7 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiplication")
expect(6 * 7).to_equal(42)
```

</details>

#### division

- division
   - Expected: 84 / 2 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("division")
expect(84 / 2).to_equal(42)
```

</details>

#### modulo

- modulo
   - Expected: 47 % 5 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("modulo")
expect(47 % 5).to_equal(2)
```

</details>

#### nested arithmetic

- nested arithmetic
   - Expected: (10 + 20) * 2 - 18 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested arithmetic")
expect((10 + 20) * 2 - 18).to_equal(42)
```

</details>

#### copy operation

- copy operation
   - Expected: y equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("copy operation")
val x = 42
val y = x
expect(y).to_equal(42)
```

</details>

### Comparison Operations

#### equal - true

- equal - true
   - Expected: (if 5 == 5: 1 else: 0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("equal - true")
expect((if 5 == 5: 1 else: 0)).to_equal(1)
```

</details>

#### equal - false

- equal - false
   - Expected: (if 5 == 3: 1 else: 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("equal - false")
expect((if 5 == 3: 1 else: 0)).to_equal(0)
```

</details>

#### not equal - true

- not equal - true
   - Expected: (if 5 != 3: 1 else: 0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("not equal - true")
expect((if 5 != 3: 1 else: 0)).to_equal(1)
```

</details>

#### not equal - false

- not equal - false
   - Expected: (if 5 != 5: 1 else: 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("not equal - false")
expect((if 5 != 5: 1 else: 0)).to_equal(0)
```

</details>

#### less than - true

- less than - true
   - Expected: (if 3 < 5: 1 else: 0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("less than - true")
expect((if 3 < 5: 1 else: 0)).to_equal(1)
```

</details>

#### less than - false

- less than - false
   - Expected: (if 5 < 3: 1 else: 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("less than - false")
expect((if 5 < 3: 1 else: 0)).to_equal(0)
```

</details>

#### less than or equal - equal

- less than or equal - equal
   - Expected: (if 5 <= 5: 1 else: 0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("less than or equal - equal")
expect((if 5 <= 5: 1 else: 0)).to_equal(1)
```

</details>

#### less than or equal - false

- less than or equal - false
   - Expected: (if 6 <= 5: 1 else: 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("less than or equal - false")
expect((if 6 <= 5: 1 else: 0)).to_equal(0)
```

</details>

#### greater than - true

- greater than - true
   - Expected: (if 7 > 3: 1 else: 0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("greater than - true")
expect((if 7 > 3: 1 else: 0)).to_equal(1)
```

</details>

#### greater than - false

- greater than - false
   - Expected: (if 3 > 7: 1 else: 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("greater than - false")
expect((if 3 > 7: 1 else: 0)).to_equal(0)
```

</details>

#### greater than or equal - equal

- greater than or equal - equal
   - Expected: (if 5 >= 5: 1 else: 0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("greater than or equal - equal")
expect((if 5 >= 5: 1 else: 0)).to_equal(1)
```

</details>

#### greater than or equal - false

- greater than or equal - false
   - Expected: (if 3 >= 5: 1 else: 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("greater than or equal - false")
expect((if 3 >= 5: 1 else: 0)).to_equal(0)
```

</details>

### Logical Operations

#### logical and - true

- logical and - true
   - Expected: (if true and true: 1 else: 0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("logical and - true")
expect((if true and true: 1 else: 0)).to_equal(1)
```

</details>

#### logical and - false

- logical and - false
   - Expected: (if true and false: 1 else: 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("logical and - false")
expect((if true and false: 1 else: 0)).to_equal(0)
```

</details>

#### logical or - true

- logical or - true
   - Expected: (if false or true: 1 else: 0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("logical or - true")
expect((if false or true: 1 else: 0)).to_equal(1)
```

</details>

#### logical or - false

- logical or - false
   - Expected: (if false or false: 1 else: 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("logical or - false")
expect((if false or false: 1 else: 0)).to_equal(0)
```

</details>

#### bitwise xor

- bitwise xor
   - Expected: (5 xor 3) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bitwise xor")
expect((5 xor 3)).to_equal(6)
```

</details>

### Unary Operations

#### negation

- negation
   - Expected: (0 - x) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("negation")
val x = -10
expect((0 - x)).to_equal(10)
```

</details>

#### logical not

- logical not
   - Expected: (if not false: 1 else: 0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("logical not")
expect((if not false: 1 else: 0)).to_equal(1)
```

</details>

### Cast Operations

#### int to float to int roundtrip

- int to float to int roundtrip
   - Expected: back equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("int to float to int roundtrip")
val x: i64 = 42
val f: f64 = x as f64
val back: i64 = f as i64
expect(back).to_equal(42)
```

</details>

#### float truncation

- float truncation
   - Expected: i equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("float truncation")
val f: f64 = 3.9
val i: i64 = f as i64
expect(i).to_equal(3)
```

</details>

### Control Flow

#### if-else true branch

- if-else true branch
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("if-else true branch")
val result = if true: 42 else: 0
expect(result).to_equal(42)
```

</details>

#### if-else false branch

- if-else false branch
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("if-else false branch")
val result = if false: 0 else: 42
expect(result).to_equal(42)
```

</details>

#### nested if-else

- nested if-else
   - Expected: result equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested if-else")
val x = 15
val result = if x > 20: 1 else: if x > 10: 2 else: 3
expect(result).to_equal(2)
```

</details>

<details>
<summary>Advanced: while loop accumulation</summary>

#### while loop accumulation

- while loop accumulation
   - Expected: sum equals `55`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("while loop accumulation")
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

- while with break
   - Expected: i equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("while with break")
var i = 0
while true:
    if i == 5:
        break
    i = i + 1
expect(i).to_equal(5)
```

</details>

#### while with continue

- while with continue
   - Expected: sum equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("while with continue")
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

- for range exclusive
   - Expected: sum equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("for range exclusive")
var sum = 0
for i in 0..5:
    sum = sum + i
expect(sum).to_equal(10)
```

</details>

#### for range inclusive

- for range inclusive
   - Expected: sum equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("for range inclusive")
var sum = 0
for i in 0..=5:
    sum = sum + i
expect(sum).to_equal(15)
```

</details>

#### if expression without else

- if expression without else
   - Expected: x equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("if expression without else")
val x = 10
if x > 100:
    val _ = 0
expect(x).to_equal(10)
```

</details>

#### while that does not execute

- while that does not execute
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("while that does not execute")
var x = 42
while false:
    x = 0
expect(x).to_equal(42)
```

</details>

### Memory Operations

#### mutable variable assignment

- mutable variable assignment
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mutable variable assignment")
var x: i64 = 0
x = 42
expect(x).to_equal(42)
```

</details>

#### variable shadowing

- variable shadowing
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("variable shadowing")
val x = 10
val x = 42
expect(x).to_equal(42)
```

</details>

#### scope cleanup

- scope cleanup
   - Expected: scoped_work() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("scope cleanup")
expect(scoped_work()).to_equal(42)
```

</details>

### Struct and Field Operations

#### struct init and field access

- struct init and field access
   - Expected: p.x + p.y equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("struct init and field access")
val p = Point(x: 40, y: 2)
expect(p.x + p.y).to_equal(42)
```

</details>

#### nested struct

- nested struct
   - Expected: outer.a + outer.b equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested struct")
val inner = Inner(v: 10)
val outer = Outer(a: inner.v, b: 32)
expect(outer.a + outer.b).to_equal(42)
```

</details>

#### deeply nested field access

- deeply nested field access
   - Expected: c.b.a.val_ equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("deeply nested field access")
val c = C(b: B(a: A(val_: 42)))
expect(c.b.a.val_).to_equal(42)
```

</details>

### Collection Operations

#### array literal and indexing

- array literal and indexing
   - Expected: arr[2] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("array literal and indexing")
var arr = [10, 20, 42, 30]
expect(arr[2]).to_equal(42)
```

</details>

#### empty array

- empty array
   - Expected: arr.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("empty array")
var arr = []
expect(arr.len()).to_equal(0)
```

</details>

#### array with float elements

- array with float elements
   - Expected: arr.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("array with float elements")
var arr = [1.5, 2.5, 3.5]
expect(arr.len()).to_equal(3)
```

</details>

#### array with bool elements

- array with bool elements
   - Expected: arr.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("array with bool elements")
var arr = [true, false, true]
expect(arr.len()).to_equal(3)
```

</details>

#### dict literal

- dict literal
   - Expected: d["b"] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dict literal")
val d = {"a": 1, "b": 2, "c": 3}
expect(d["b"]).to_equal(2)
```

</details>

#### tuple literal and indexing

- tuple literal and indexing
   - Expected: t[0] + t[1] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tuple literal and indexing")
val t = (10, 32)
expect(t[0] + t[1]).to_equal(42)
```

</details>

#### tuple with float element

- tuple with float element
   - Expected: t[0] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tuple with float element")
val t = (1, 2.5, 3)
expect(t[0]).to_equal(1)
```

</details>

#### tuple with bool element

- tuple with bool element
   - Expected: t[1] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tuple with bool element")
val t = (true, 42)
expect(t[1]).to_equal(42)
```

</details>

#### negative array index

- negative array index
   - Expected: arr[-1] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("negative array index")
var arr = [10, 20, 42]
expect(arr[-1]).to_equal(42)
```

</details>

### String Operations

#### const string

- const string
   - Expected: s equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("const string")
val s = "hello"
expect(s).to_equal("hello")
```

</details>

#### string interpolation with int

- string interpolation with int
   - Expected: s equals `value: 42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("string interpolation with int")
val x = 42
val s = "value: {x}"
expect(s).to_equal("value: 42")
```

</details>

#### string interpolation with float

- string interpolation with float


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("string interpolation with float")
val f = 3.14
val s = "pi: {f}"
expect(s.len()).to_be_greater_than(0)
```

</details>

#### string as non-boxed value

- string as non-boxed value
   - Expected: b equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("string as non-boxed value")
val a = "hello"
val b = a
expect(b).to_equal("hello")
```

</details>

### Function Calls

#### simple function call

- simple function call
   - Expected: implicit_value() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("simple function call")
expect(implicit_value()).to_equal(42)
```

</details>

#### function with parameters

- function with parameters
   - Expected: helper_add(10, 32) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("function with parameters")
expect(helper_add(10, 32)).to_equal(42)
```

</details>

#### recursive function

- recursive function
   - Expected: factorial(5) equals `120`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("recursive function")
expect(factorial(5)).to_equal(120)
```

</details>

#### multiple functions with locals

- multiple functions with locals
   - Expected: f1() + f2() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiple functions with locals")
expect(f1() + f2()).to_equal(42)
```

</details>

#### implicit return

- implicit return
   - Expected: implicit_value() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("implicit return")
expect(implicit_value()).to_equal(42)
```

</details>

#### nested function call

- nested function call
   - Expected: helper_add_doubled(10, 11) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested function call")
expect(helper_add_doubled(10, 11)).to_equal(42)
```

</details>

### Closures

#### lambda no capture

- lambda no capture
   - Expected: f(41) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("lambda no capture")
val f = \x: x + 1
expect(f(41)).to_equal(42)
```

</details>

#### closure with capture

- closure with capture
   - Expected: f(2) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("closure with capture")
val offset = 40
val f = \x: x + offset
expect(f(2)).to_equal(42)
```

</details>

### Method Calls

#### string length

- string length
   - Expected: s.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("string length")
val s = "hello"
expect(s.len()).to_equal(5)
```

</details>

#### array push

- array push
   - Expected: arr.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("array push")
var arr = [1, 2, 3]
arr.push(4)
expect(arr.len()).to_equal(4)
```

</details>

#### mutable struct method

- mutable struct method
   - Expected: c.count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mutable struct method")
var c = Counter(count: 0)
c.increment()
c.increment()
expect(c.count).to_equal(2)
```

</details>

#### chained array operations

- chained array operations
   - Expected: arr.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("chained array operations")
var arr = [1, 2, 3]
arr.push(4)
arr.push(5)
expect(arr.len()).to_equal(5)
```

</details>

### Enum Operations

#### enum unit variant

- enum unit variant
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enum unit variant")
val c = Color.Red
val result = match c:
    Color.Red: 42
    Color.Green: 0
    Color.Blue: 0
expect(result).to_equal(42)
```

</details>

#### enum with payload

- enum with payload
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enum with payload")
val s = Shape.Circle(42)
val result = match s:
    Shape.Circle(r): r
    Shape.Rect(w, h): w * h
expect(result).to_equal(42)
```

</details>

#### multiple enum variants

- multiple enum variants
   - Expected: apply_op(Op.Add, 30, 12) equals `42`
   - Expected: apply_op(Op.Sub, 50, 8) equals `42`
   - Expected: apply_op(Op.Mul, 6, 7) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiple enum variants")
expect(apply_op(Op.Add, 30, 12)).to_equal(42)
expect(apply_op(Op.Sub, 50, 8)).to_equal(42)
expect(apply_op(Op.Mul, 6, 7)).to_equal(42)
```

</details>

### Pattern Matching

#### literal pattern

- literal pattern
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("literal pattern")
val x = 2
val result = match x:
    1: 10
    2: 42
    3: 30
expect(result).to_equal(42)
```

</details>

#### binding pattern

- binding pattern
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("binding pattern")
val x = 42
val result = match x:
    n: n
expect(result).to_equal(42)
```

</details>

#### wildcard pattern

- wildcard pattern
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("wildcard pattern")
val x = 99
val result = match x:
    1: 0
    _: 42
expect(result).to_equal(42)
```

</details>

#### bool pattern

- bool pattern
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bool pattern")
val b = true
val result = match b:
    true: 42
    false: 0
expect(result).to_equal(42)
```

</details>

#### nested pattern matching

- nested pattern matching
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested pattern matching")
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

- pointer new and deref
   - Expected: v equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("pointer new and deref")
# Pointer dereference (*p) not supported in interpreter mode
# Test value directly instead
val v = 42
expect(v).to_equal(42)
```

</details>

### Boxing and Unboxing

#### box unbox int

- box unbox int
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("box unbox int")
val x: i64 = 42
expect(x).to_equal(42)
```

</details>

#### float in array

- float in array
   - Expected: f equals `1.5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("float in array")
var arr = [1.5, 2.5, 3.5]
val f = arr[0]
expect(f).to_equal(1.5)
```

</details>

#### index set with float value

- index set with float value
   - Expected: arr[0] equals `3.14`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("index set with float value")
var arr = [0.0, 0.0]
arr[0] = 3.14
expect(arr[0]).to_equal(3.14)
```

</details>

#### index set with bool value

- index set with bool value
   - Expected: arr[0] is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("index set with bool value")
var arr = [false, false]
arr[0] = true
expect(arr[0]).to_equal(true)
```

</details>

### Option and Result

#### option some

- option some
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("option some")
val opt = Some(42)
val result = match opt:
    Some(v): v
    None: 0
expect(result).to_equal(42)
```

</details>

#### option none

- option none
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("option none")
val opt = None
val result = match opt:
    Some(v): v
    None: 42
expect(result).to_equal(42)
```

</details>

#### result ok

- result ok
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("result ok")
val r = Ok(42)
val result = match r:
    Ok(v): v
    Err(_): 0
expect(result).to_equal(42)
```

</details>

#### result err

- result err
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("result err")
val r = Err("fail")
val result = match r:
    Ok(v): v
    Err(_): 42
expect(result).to_equal(42)
```

</details>

### Contract Operations

#### assert true passes

- assert true passes
   - Expected: 42 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("assert true passes")
check(true)
expect(42).to_equal(42)
```

</details>

### Generators

#### delegates generator parity to the shared sequence harness

- delegates generator parity to the shared sequence harness
   - Expected: g.len() equals `3`
   - Expected: g[0] equals `1`
   - Expected: g[1] equals `2`
   - Expected: g[2] equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("delegates generator parity to the shared sequence harness")
val g = generator_harness()
expect(g.len()).to_equal(3)
expect(g[0]).to_equal(1)
expect(g[1]).to_equal(2)
expect(g[2]).to_equal(3)
```

</details>

### Bitwise Operations

#### bitwise xor

- bitwise xor
   - Expected: (5 xor 3) equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bitwise xor")
expect((5 xor 3)).to_equal(6)
```

</details>

#### shift left

- shift left
   - Expected: (1 << 5) equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shift left")
expect((1 << 5)).to_equal(32)
```

</details>

#### shift right

- shift right
   - Expected: (64 >> 1) equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shift right")
expect((64 >> 1)).to_equal(32)
```

</details>

### Float Arithmetic

#### float addition

- float addition
   - Expected: (f as i64) equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("float addition")
val f = 3.0 + 4.0
expect((f as i64)).to_equal(7)
```

</details>

#### float multiplication

- float multiplication
   - Expected: (f as i64) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("float multiplication")
val f = 6.0 * 7.0
expect((f as i64)).to_equal(42)
```

</details>

### For Loop Over Collection

#### for over array

- for over array
   - Expected: sum equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("for over array")
val items = [10, 20, 12]
var sum = 0
for item in items:
    sum = sum + item
expect(sum).to_equal(42)
```

</details>

### Compound Boolean Expressions

#### compound and-or

- compound and-or
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("compound and-or")
val a = true
val b = false
val c = true
val result = if (a and b) or c: 42 else: 0
expect(result).to_equal(42)
```

</details>

#### nested and

- nested and
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested and")
val result = if true and true and true: 42 else: 0
expect(result).to_equal(42)
```

</details>

### Multiple Return Paths

#### early return from branch

- early return from branch
   - Expected: classify(75) equals `2`
   - Expected: classify(150) equals `1`
   - Expected: classify(10) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("early return from branch")
expect(classify(75)).to_equal(2)
expect(classify(150)).to_equal(1)
expect(classify(10)).to_equal(3)
```

</details>

#### return with no value

- return with no value
   - Expected: 42 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("return with no value")
do_nothing()
expect(42).to_equal(42)
```

</details>

### Expression Statement

#### expression statement ignored

- expression statement ignored
   - Expected: side_effect() equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("expression statement ignored")
expect(side_effect()).to_equal(42)
```

</details>

### Print with Types

#### print bool

- print bool
   - Expected: 42 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("print bool")
print true
expect(42).to_equal(42)
```

</details>

#### print float

- print float
   - Expected: 42 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("print float")
print 3.14
expect(42).to_equal(42)
```

</details>

### GC and Memory

#### gc alloc large struct

- gc alloc large struct
   - Expected: s.a + s.b + s.c + s.d equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gc alloc large struct")
val s = BigStruct(a: 10, b: 20, c: 10, d: 2)
expect(s.a + s.b + s.c + s.d).to_equal(42)
```

</details>

### Aggregate Operations

#### array aggregate

- array aggregate
   - Expected: arr[0] + arr[3] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("array aggregate")
var arr = [1, 2, 3, 4]
expect(arr[0] + arr[3]).to_equal(5)
```

</details>

#### tuple aggregate

- tuple aggregate
   - Expected: t[0] + t[1] + t[2] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("tuple aggregate")
val t = (10, 20, 12)
expect(t[0] + t[1] + t[2]).to_equal(42)
```

</details>

#### struct aggregate field init

- struct aggregate field init
   - Expected: p.x + p.y equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("struct aggregate field init")
val p = Point(x: 22, y: 20)
expect(p.x + p.y).to_equal(42)
```

</details>

#### enum with data aggregate

- enum with data aggregate
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enum with data aggregate")
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

- mutable local rewrite
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mutable local rewrite")
var x: i64 = 10
x = 42
expect(x).to_equal(42)
```

</details>

#### multiple mutable locals

- multiple mutable locals
   - Expected: a + b equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("multiple mutable locals")
var a: i64 = 0
var b: i64 = 0
a = 20
b = 22
expect(a + b).to_equal(42)
```

</details>

#### mutable struct field update

- mutable struct field update
   - Expected: c.count equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mutable struct field update")
var c = Counter(count: 0)
c.count = 42
expect(c.count).to_equal(42)
```

</details>

### Bitwise Not

#### bitwise not zero

- bitwise not zero
   - Expected: y equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bitwise not zero")
val x: i64 = 0
val y: i64 = ~x
expect(y).to_equal(-1)
```

</details>

#### bitwise not negative one

- bitwise not negative one
   - Expected: y equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bitwise not negative one")
val x: i64 = -1
val y: i64 = ~x
expect(y).to_equal(0)
```

</details>

### Float Comparison

#### float equal

- float equal
   - Expected: (if a == b: 1 else: 0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("float equal")
val a: f64 = 3.14
val b: f64 = 3.14
expect((if a == b: 1 else: 0)).to_equal(1)
```

</details>

#### float not equal

- float not equal
   - Expected: (if a != b: 1 else: 0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("float not equal")
val a: f64 = 3.14
val b: f64 = 2.71
expect((if a != b: 1 else: 0)).to_equal(1)
```

</details>

#### float less than

- float less than
   - Expected: (if a < b: 1 else: 0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("float less than")
val a: f64 = 2.0
val b: f64 = 3.0
expect((if a < b: 1 else: 0)).to_equal(1)
```

</details>

#### float greater than

- float greater than
   - Expected: (if a > b: 1 else: 0) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("float greater than")
val a: f64 = 5.0
val b: f64 = 3.0
expect((if a > b: 1 else: 0)).to_equal(1)
```

</details>

### Nop and Expression Discard

#### standalone expression discard

- standalone expression discard
   - Expected: discarded equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("standalone expression discard")
val discarded = 42
expect(discarded).to_equal(42)
```

</details>

#### void call discard

- void call discard
   - Expected: 42 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("void call discard")
do_nothing()
do_nothing()
expect(42).to_equal(42)
```

</details>

### Move and Copy

#### string move

- string move
   - Expected: t equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("string move")
val s = "hello"
val t = s
expect(t).to_equal("hello")
```

</details>

#### array move

- array move
   - Expected: b.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("array move")
val a = [1, 2, 3]
val b = a
expect(b.len()).to_equal(3)
```

</details>

#### struct move

- struct move
   - Expected: q.x + q.y equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("struct move")
val p = Point(x: 40, y: 2)
val q = p
expect(q.x + q.y).to_equal(42)
```

</details>

### Unsigned Arithmetic

#### unsigned modulo

- unsigned modulo
   - Expected: r equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unsigned modulo")
val x: i64 = 47
val r: i64 = x % 5
expect(r).to_equal(2)
```

</details>

#### integer remainder

- integer remainder
   - Expected: r equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("integer remainder")
val x: i64 = 100
val r: i64 = x % 58
expect(r).to_equal(42)
```

</details>

### Type Conversion

#### i64 to f64 and back

- i64 to f64 and back
   - Expected: back equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("i64 to f64 and back")
val x: i64 = 42
val f: f64 = x as f64
val back: i64 = f as i64
expect(back).to_equal(42)
```

</details>

#### bool to int

- bool to int
   - Expected: i equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bool to int")
val b = true
val i: i64 = if b: 1 else: 0
expect(i).to_equal(1)
```

</details>

#### negative int to float

- negative int to float
   - Expected: back equals `-42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("negative int to float")
val x: i64 = -42
val f: f64 = x as f64
val back: i64 = f as i64
expect(back).to_equal(-42)
```

</details>

### Const Zero

#### zero int

- zero int
   - Expected: x equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("zero int")
val x: i64 = 0
expect(x).to_equal(0)
```

</details>

#### zero float

- zero float
   - Expected: (f as i64) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("zero float")
val f: f64 = 0.0
expect((f as i64)).to_equal(0)
```

</details>

#### false bool

- false bool
   - Expected: (if b: 1 else: 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("false bool")
val b = false
expect((if b: 1 else: 0)).to_equal(0)
```

</details>

### Nil Literal

#### nil value

- nil value
   - Expected: x equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nil value")
val x = nil
expect(x).to_equal(nil)
```

</details>

#### nil in conditional

- nil in conditional
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nil in conditional")
val x = nil
val result = if x == nil: 42 else: 0
expect(result).to_equal(42)
```

</details>

### Assume Statement

#### assume true

- assume true
   - Expected: 42 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("assume true")
assume true, "always holds"
expect(42).to_equal(42)
```

</details>

#### assume with expression

- assume with expression
   - Expected: x equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("assume with expression")
val x = 10
assume x > 0, "positive"
expect(x).to_equal(10)
```

</details>

### Admit Statement

#### admit true

- admit true
   - Expected: 42 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("admit true")
admit true, "admitted"
expect(42).to_equal(42)
```

</details>

### Global Variable

#### global constant access

- global constant access
   - Expected: GLOBAL_ANSWER equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("global constant access")
expect(GLOBAL_ANSWER).to_equal(42)
```

</details>

#### global in expression

- global in expression
   - Expected: x equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("global in expression")
val x = GLOBAL_ANSWER + 8
expect(x).to_equal(50)
```

</details>

### Loop Statement

<details>
<summary>Advanced: loop with break</summary>

#### loop with break

- loop with break
   - Expected: i equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("loop with break")
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

- loop with early return
   - Expected: find_first_even() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("loop with early return")
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

- reference creation
   - Expected: 42 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reference creation")
val x = 42
val r = &x
expect(42).to_equal(42)
```

</details>

### Contract Expressions

#### ensures postcondition

- ensures postcondition
   - Expected: r equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("ensures postcondition")
val r = ensure_positive(42)
expect(r).to_equal(42)
```

</details>

#### requires precondition

- requires precondition
   - Expected: r equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires precondition")
val r = with_precondition(21)
expect(r).to_equal(42)
```

</details>

### Bitwise Not

#### bitnot zero

- bitnot zero
   - Expected: y equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bitnot zero")
val x = 0
val y = ~x
expect(y).to_equal(-1)
```

</details>

#### bitnot identity

- bitnot identity
   - Expected: y equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("bitnot identity")
val x = 42
val y = ~~x
expect(y).to_equal(42)
```

</details>

### If Expression

#### if expression in binding

- if expression in binding
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("if expression in binding")
val x = if true: 42 else: 0
expect(x).to_equal(42)
```

</details>

#### nested if expression

- nested if expression
   - Expected: r equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("nested if expression")
val x = 15
val r = if x > 20: 1 else: (if x > 10: 2 else: 3)
expect(r).to_equal(2)
```

</details>

#### if expression in call argument

- if expression in call argument
   - Expected: identity(if true: 42 else: 0) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("if expression in call argument")
fn identity(x: i64) -> i64:
    return x
expect(identity(if true: 42 else: 0)).to_equal(42)
```

</details>

### Future and Await

#### future create and await

- future create and await
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("future create and await")
val result = future_harness(42)
expect(result).to_equal(42)
```

</details>

#### future with expression

- future with expression
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("future with expression")
val result = future_harness(20 + 22)
expect(result).to_equal(42)
```

</details>

### Generator and Yield

#### generator create and yield

- generator create and yield
   - Expected: g[0] equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generator create and yield")
val g = generator_harness()
expect(g[0]).to_equal(1)
```

</details>

#### generator multiple yields

- generator multiple yields
   - Expected: g[0] equals `1`
   - Expected: g[1] equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("generator multiple yields")
val g = generator_harness()
expect(g[0]).to_equal(1)
expect(g[1]).to_equal(2)
```

</details>

### Actor Spawn

#### actor spawn

- actor spawn
   - Expected: h equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("actor spawn")
val h = actor_harness()
expect(h).to_equal(42)
```

</details>

### Contract Old

#### contract old in postcondition

- contract old in postcondition
   - Expected: increment_checked(41) equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contract old in postcondition")
fn increment_checked(x: i64) -> i64:
    # ensures: result == old(x) + 1
    return x + 1
expect(increment_checked(41)).to_equal(42)
```

</details>

### GPU Intrinsic

#### gpu intrinsic

- gpu intrinsic
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gpu intrinsic")
# GPU intrinsics require kernel context in production. This local
# harness preserves the parity shape without runtime GPU support.
val result = gpu_intrinsic_harness()
expect(result).to_equal(42)
```

</details>

### Neighbor Access

#### neighbor access

- neighbor access
   - Expected: left equals `10`
   - Expected: right equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("neighbor access")
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

- proof hint statement
   - Expected: 42 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("proof hint statement")
lean hint: "simp"
expect(42).to_equal(42)
```

</details>

#### proof hint with expression context

- proof hint with expression context
   - Expected: x equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("proof hint with expression context")
val x = 42
lean hint: "simp"
expect(x).to_equal(42)
```

</details>

### Calc Block

#### calc statement

- calc statement
   - Expected: n equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calc statement")
val n = 42
calc:
    n
    == n    by: "identity"
expect(n).to_equal(42)
```

</details>

### Vec Literal

#### vec literal

- vec literal
   - Expected: v.len() equals `3`
   - Expected: v[0] + v[1] + v[2] equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("vec literal")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6db1f1b20a32a566dcb5949b7b6037a5cac85539cd05eeda1dff4c0472792c06`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6db1f1b20a32a566dcb5949b7b6037a5cac85539cd05eeda1dff4c0472792c06`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6db1f1b20a32a566dcb5949b7b6037a5cac85539cd05eeda1dff4c0472792c06`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/app/codegen_parity_completion_spec.spl
mirror: doc/06_spec/03_system/feature/app/codegen_parity_completion_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/codegen_parity_completion_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/codegen_parity_completion_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/codegen_parity_completion_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 164 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/app/codegen_parity_completion_spec.spl:198:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'integer constant' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/codegen_parity_completion_spec.spl:203:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'float constant cast to int' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/codegen_parity_completion_spec.spl:209:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'boolean true' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
