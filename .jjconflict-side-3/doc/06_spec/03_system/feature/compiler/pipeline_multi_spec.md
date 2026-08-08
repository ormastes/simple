# Pipeline Multi-File Compilation

> Tests the multi-file compilation pipeline including module resolution, cross-file references, and incremental compilation. Verifies that the compiler correctly handles projects with multiple source files and inter-module dependencies.

<!-- sdn-diagram:id=pipeline_multi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pipeline_multi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pipeline_multi_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pipeline_multi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 51 | 51 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pipeline Multi-File Compilation

Tests the multi-file compilation pipeline including module resolution, cross-file references, and incremental compilation. Verifies that the compiler correctly handles projects with multiple source files and inter-module dependencies.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/pipeline_multi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the multi-file compilation pipeline including module resolution, cross-file
references, and incremental compilation. Verifies that the compiler correctly
handles projects with multiple source files and inter-module dependencies.

## Scenarios

### Pipeline Multi - Return Values

#### return 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    0\n")
    expect(code).to_equal(0)
```

</details>

#### return 42

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    42\n")
    expect(code).to_equal(42)
```

</details>

#### explicit return statement

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    return 0\n")
    expect(code).to_equal(0)
```

</details>

#### simple arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    1 + 2\n")
    expect(code).to_equal(3)
```

</details>

#### nested arithmetic

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    (10 + 20) * 2\n")
    expect(code).to_equal(60)
```

</details>

#### variable declaration

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    val x = 5\n    x + 3\n")
    expect(code).to_equal(8)
```

</details>

#### if-else expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    val x = 10\n    if x > 5:\n        1\n    else:\n        0\n")
    expect(code).to_equal(1)
```

</details>

<details>
<summary>Advanced: while loop</summary>

#### while loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    var x = 0\n    while x < 10:\n        x = x + 1\n    x\n")
    expect(code).to_equal(10)
```

</details>


</details>

#### multiple variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    val a = 10\n    val b = 20\n    val c = a + b\n    c\n")
    expect(code).to_equal(30)
```

</details>

#### nested if-else

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    val x = 15\n    if x > 20:\n        3\n    else:\n        if x > 10:\n            2\n        else:\n            1\n")
    expect(code).to_equal(2)
```

</details>

#### factorial 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    var n = 5\n    var result = 1\n    while n > 0:\n        result = result * n\n        n = n - 1\n    result\n")
    expect(code).to_equal(120)
```

</details>

#### subtraction

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    val x = 100\n    val y = 58\n    x - y\n")
    expect(code).to_equal(42)
```

</details>

#### var decrement in while

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    var x = 50\n    while x > 10:\n        x = x - 5\n    x\n")
    expect(code).to_equal(10)
```

</details>

#### sum 1..5

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    var sum = 0\n    var i = 1\n    while i <= 5:\n        sum = sum + i\n        i = i + 1\n    sum\n")
    expect(code).to_equal(15)
```

</details>

#### greater-than-or-equal operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    val x = 10\n    if x >= 10:\n        1\n    else:\n        0\n")
    expect(code).to_equal(1)
```

</details>

#### equality operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    val x = 5\n    if x == 5:\n        42\n    else:\n        0\n")
    expect(code).to_equal(42)
```

</details>

#### inequality operator

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    val x = 5\n    if x != 3:\n        1\n    else:\n        0\n")
    expect(code).to_equal(1)
```

</details>

### Pipeline Multi - Functions

#### function call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn add(a: i64, b: i64) -> i64:\n    a + b\n\nfn main():\n    add(10, 20)\n")
    expect(code).to_equal(30)
```

</details>

#### nested function calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn double(x: i64) -> i64:\n    x * 2\n\nfn main():\n    double(double(5))\n")
    expect(code).to_equal(20)
```

</details>

#### recursion fibonacci(6)=8

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn fib(n: i64) -> i64:\n    if n <= 1:\n        n\n    else:\n        fib(n - 1) + fib(n - 2)\n\nfn main():\n    fib(6)\n")
    expect(code).to_equal(8)
```

</details>

#### multiple functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn square(x: i64) -> i64:\n    x * x\n\nfn add_squares(a: i64, b: i64) -> i64:\n    square(a) + square(b)\n\nfn main():\n    add_squares(3, 4)\n")
    expect(code).to_equal(25)
```

</details>

#### division

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    val x = 100\n    val y = 4\n    x / y\n")
    expect(code).to_equal(25)
```

</details>

#### modulo

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    val x = 17\n    val y = 5\n    x % y\n")
    expect(code).to_equal(2)
```

</details>

#### deep recursion fibonacci(10)=55

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn fib(n: i64) -> i64:\n    if n <= 1:\n        n\n    else:\n        fib(n - 1) + fib(n - 2)\n\nfn main():\n    fib(10)\n")
    expect(code).to_equal(55)
```

</details>

#### 3-argument function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn add3(a: i64, b: i64, c: i64) -> i64:\n    a + b + c\n\nfn main():\n    add3(10, 20, 30)\n")
    expect(code).to_equal(60)
```

</details>

#### call chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn inc(x: i64) -> i64:\n    x + 1\n\nfn main():\n    inc(inc(inc(inc(0))))\n")
    expect(code).to_equal(4)
```

</details>

#### GCD algorithm

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn gcd(a: i64, b: i64) -> i64:\n    if b == 0:\n        a\n    else:\n        gcd(b, a % b)\n\nfn main():\n    gcd(48, 18)\n")
    expect(code).to_equal(6)
```

</details>

<details>
<summary>Advanced: power of 2 via loop</summary>

#### power of 2 via loop

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    var result = 1\n    var i = 0\n    while i < 7:\n        result = result * 2\n        i = i + 1\n    result\n")
    expect(code).to_equal(128)
```

</details>


</details>

#### register pressure test

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn identity(x: i64) -> i64:\n    x\n\nfn main():\n    val a = 1\n    val b = 2\n    val c = 3\n    val d = 4\n    val e = 5\n    val f = identity(10)\n    val g = identity(20)\n    a + b + c + d + e + f + g\n")
    expect(code).to_equal(45)
```

</details>

#### 4-argument function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn sum4(a: i64, b: i64, c: i64, d: i64) -> i64:\n    a + b + c + d\n\nfn main():\n    sum4(10, 20, 30, 40)\n")
    expect(code).to_equal(100)
```

</details>

#### spill across calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn id(x: i64) -> i64:\n    x\n\nfn main():\n    val a = 1\n    val b = 2\n    val c = 3\n    val d = 4\n    val e = 5\n    val f = 6\n    val g = 7\n    val h = id(a + b)\n    a + b + c + d + e + f + g + h\n")
    expect(code).to_equal(31)
```

</details>

#### mutual recursion is_even(10)=1

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn is_even(n: i64) -> i64:\n    if n == 0:\n        1\n    else:\n        is_odd(n - 1)\n\nfn is_odd(n: i64) -> i64:\n    if n == 0:\n        0\n    else:\n        is_even(n - 1)\n\nfn main():\n    is_even(10)\n")
    expect(code).to_equal(1)
```

</details>

#### Collatz steps for 6

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn collatz_steps(n: i64) -> i64:\n    var steps = 0\n    var x = n\n    while x != 1:\n        if x % 2 == 0:\n            x = x / 2\n        else:\n            x = x * 3 + 1\n        steps = steps + 1\n    steps\n\nfn main():\n    collatz_steps(6)\n")
    expect(code).to_equal(8)
```

</details>

#### 5-argument function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn sum5(a: i64, b: i64, c: i64, d: i64, e: i64) -> i64:\n    a + b + c + d + e\n\nfn main():\n    sum5(1, 2, 3, 4, 5)\n")
    expect(code).to_equal(15)
```

</details>

<details>
<summary>Advanced: nested while loops (3x4=12)</summary>

#### nested while loops (3x4=12)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    var total = 0\n    var i = 0\n    while i < 3:\n        var j = 0\n        while j < 4:\n            total = total + 1\n            j = j + 1\n        i = i + 1\n    total\n")
    expect(code).to_equal(12)
```

</details>


</details>

#### boolean range check

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn in_range(x: i64, lo: i64, hi: i64) -> i64:\n    if x >= lo:\n        if x <= hi:\n            1\n        else:\n            0\n    else:\n        0\n\nfn main():\n    in_range(5, 3, 10) + in_range(15, 3, 10) + in_range(3, 3, 10)\n")
    expect(code).to_equal(2)
```

</details>

#### Ackermann(2,3)=9

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn ack(m: i64, n: i64) -> i64:\n    if m == 0:\n        n + 1\n    else:\n        if n == 0:\n            ack(m - 1, 1)\n        else:\n            ack(m - 1, ack(m, n - 1))\n\nfn main():\n    ack(2, 3)\n")
    expect(code).to_equal(9)
```

</details>

### Pipeline Multi - String Output

#### puts Hello

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, out) = compile_and_run("extern fn puts(s: text) -> i64\n\nfn main():\n    puts(\"Hello\")\n    0\n")
    expect(out).to_equal("Hello\n")
```

</details>

#### multiple puts calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, out) = compile_and_run("extern fn puts(s: text) -> i64\n\nfn main():\n    puts(\"foo\")\n    puts(\"bar\")\n    0\n")
    expect(out).to_equal("foo\nbar\n")
```

</details>

#### puts and return value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, out) = compile_and_run("extern fn puts(s: text) -> i64\n\nfn main():\n    puts(\"done\")\n    42\n")
    expect(code).to_equal(42)
```

</details>

#### printf with int arg

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, out) = compile_and_run("extern fn printf(fmt: text, n: i64) -> i64\nextern fn puts(s: text) -> i64\n\nfn main():\n    printf(\"%d\", 42)\n    puts(\"\")\n    0\n")
    expect(out).to_equal("42\n")
```

</details>

#### printf with 2 int args

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, out) = compile_and_run("extern fn printf(fmt: text, a: i64, b: i64) -> i64\nextern fn puts(s: text) -> i64\n\nfn main():\n    printf(\"%d+%d\", 10, 20)\n    puts(\"\")\n    0\n")
    expect(out).to_equal("10+20\n")
```

</details>

#### puts then compute

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, out) = compile_and_run("extern fn puts(s: text) -> i64\n\nfn add(a: i64, b: i64) -> i64:\n    a + b\n\nfn main():\n    puts(\"calc\")\n    add(3, 4)\n")
    expect(out).to_equal("calc\n")
```

</details>

### Pipeline Multi - Arrays

#### array index [1]

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    val arr = [10, 20, 30]\n    arr[1]\n")
    expect(code).to_equal(20)
```

</details>

#### array index [0]+[2]

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    val arr = [5, 10, 15]\n    arr[0] + arr[2]\n")
    expect(code).to_equal(20)
```

</details>

#### array with computed index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    val arr = [3, 7, 11, 13]\n    val i = 1 + 1\n    arr[i]\n")
    expect(code).to_equal(11)
```

</details>

### Pipeline Multi - Mutable Variables

#### mutable variable reassignment

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    var x = 5\n    x = x + 3\n    x\n")
    expect(code).to_equal(8)
```

</details>

#### multiple reassignments double

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    var x = 1\n    x = x + x\n    x = x + x\n    x = x + x\n    x\n")
    expect(code).to_equal(8)
```

</details>

#### compound variable operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn main():\n    var x = 10\n    x = x - 3\n    x = x * 2\n    x\n")
    expect(code).to_equal(14)
```

</details>

#### malloc heap allocation

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("extern fn malloc(size: i64) -> i64\nextern fn free(ptr: i64) -> i64\n\nfn main():\n    val ptr = malloc(8)\n    0\n")
    expect(code).to_equal(0)
```

</details>

#### array element sum via function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
skip_on_interpreter "requires native backend":
    val (code, _) = compile_and_run("fn sum3(a: i64, b: i64, c: i64) -> i64:\n    a + b + c\n\nfn main():\n    val arr = [10, 20, 30]\n    sum3(arr[0], arr[1], arr[2])\n")
    expect(code).to_equal(60)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 51 |
| Active scenarios | 51 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
