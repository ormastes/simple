# Branch Coverage Test Suite - Comprehensive Core Coverage

> Comprehensive tests to achieve 100% branch coverage of core Simple modules. Tests all execution paths in lexer, parser, interpreter, and type system.

<!-- sdn-diagram:id=branch_coverage_27_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=branch_coverage_27_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

branch_coverage_27_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=branch_coverage_27_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 81 | 81 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Branch Coverage Test Suite - Comprehensive Core Coverage

Comprehensive tests to achieve 100% branch coverage of core Simple modules. Tests all execution paths in lexer, parser, interpreter, and type system.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BRANCH #COMPREHENSIVE |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/compiler_core/branch_coverage_27_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive tests to achieve 100% branch coverage of core Simple modules.
Tests all execution paths in lexer, parser, interpreter, and type system.

## Scenarios

### Lexer All Branches

#### handles all numeric formats

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dec = 42
val hex = 0xFF
val bin = 0b1010
val oct = 0o77
check(dec == 42)
check(hex == 255)
check(bin == 10)
check(oct == 63)
```

</details>

#### handles all float formats

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val normal = 3.14
val exp_pos = 1.5e10
val exp_neg = 2.5e-5
check(normal > 3.0)
check(exp_pos > 1.0)
check(exp_neg < 1.0)
```

</details>

#### handles all string escapes

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val newline = "\n"
val tab = "\t"
val quote = "\""
val backslash = "\\"
check(newline.len() > 0)
check(tab.len() > 0)
check(quote == "\"")
check(backslash == "\\")
```

</details>

#### handles raw strings

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = r"\n\t\\"
check(raw.contains("\\"))
```

</details>

#### handles multiline strings

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val multi = """
line 1
line 2
"""
check(multi.contains("line"))
```

</details>

#### handles string interpolation - all cases

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val s1 = "{x}"
val s2 = "value: {x + 5}"
val s3 = "{x} + {x} = {x + x}"
check(s1.contains("10"))
check(s2.contains("15"))
check(s3.contains("20"))
```

</details>

### Parser All Branches

#### handles all operators - arithmetic

1. check
2. check
3. check
4. check
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(2 + 3 == 5)
check(5 - 2 == 3)
check(3 * 4 == 12)
check(10 / 2 == 5)
check(10 % 3 == 1)
check(2 ** 3 == 8)
```

</details>

#### handles all operators - comparison

1. check
2. check
3. check
4. check
5. check
6. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 == 5)
check(5 != 4)
check(5 > 4)
check(5 >= 5)
check(4 < 5)
check(4 <= 4)
```

</details>

#### handles all operators - logical

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true and true)
check(true or false)
check(not false)
```

</details>

#### handles all operators - bitwise

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((5 & 3) == 1)
check((5 | 3) == 7)
check((5 ^ 3) == 6)
```

</details>

#### handles unary operators

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(-5 < 0)
check(5 > 0)
check(not false == true)
```

</details>

#### handles precedence - all levels

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(2 + 3 * 4 == 14)
check((2 + 3) * 4 == 20)
check(2 ** 3 * 4 == 32)
check(10 - 5 - 2 == 3)
```

</details>

#### handles associativity

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(10 - 5 - 2 == 3)
check(2 ** 3 ** 2 == 512)
```

</details>

### Control Flow All Branches

#### if - then only

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var x = 0
    if true:
        x = 1
    x
check(run() == 1)
```

</details>

#### if - else taken

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var x = 0
    if false:
        x = 1
    else:
        x = 2
    x
check(run() == 2)
```

</details>

#### if - elif - first

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var x = 0
    if true:
        x = 1
    elif true:
        x = 2
    else:
        x = 3
    x
check(run() == 1)
```

</details>

#### if - elif - second

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var x = 0
    if false:
        x = 1
    elif true:
        x = 2
    else:
        x = 3
    x
check(run() == 2)
```

</details>

#### if - elif - else

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var x = 0
    if false:
        x = 1
    elif false:
        x = 2
    else:
        x = 3
    x
check(run() == 3)
```

</details>

#### nested if - all paths

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var result = 0
    if true:
        if true:
            result = 1
        else:
            result = 2
    else:
        result = 3
    result
check(run() == 1)
```

</details>

### Loop All Branches

#### for - empty range

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var count = 0
    for i in 0..0:
        count = count + 1
    count
check(run() == 0)
```

</details>

#### for - single iteration

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var count = 0
    for i in 0..1:
        count = count + 1
    count
check(run() == 1)
```

</details>

#### for - multiple iterations

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var count = 0
    for i in 0..5:
        count = count + 1
    count
check(run() == 5)
```

</details>

#### for - with break first

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var count = 0
    for i in 0..10:
        count = count + 1
        break
    count
check(run() == 1)
```

</details>

#### for - with break middle

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var count = 0
    for i in 0..10:
        count = count + 1
        if count == 5:
            break
    count
check(run() == 5)
```

</details>

#### for - with continue

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var count = 0
    for i in 0..10:
        if i % 2 == 0:
            continue
        count = count + 1
    count
check(run() == 5)
```

</details>

#### for - all continue

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var count = 0
    for i in 0..5:
        continue
        count = count + 1
    count
check(run() == 0)
```

</details>

#### while - never enters

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var count = 0
    while false:
        count = count + 1
    count
check(run() == 0)
```

</details>

#### while - enters once

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var count = 0
    while count < 1:
        count = count + 1
    count
check(run() == 1)
```

</details>

#### while - multiple times

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var count = 0
    while count < 5:
        count = count + 1
    count
check(run() == 5)
```

</details>

#### while - with break

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var count = 0
    while true:
        count = count + 1
        if count == 3:
            break
    count
check(run() == 3)
```

</details>

#### while - with continue

1. fn run
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    var count = 0
    var iter = 0
    while iter < 10:
        iter = iter + 1
        if iter % 2 == 0:
            continue
        count = count + 1
    count
check(run() == 5)
```

</details>

### Match All Branches

#### match - first case

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 1
val r = match x:
    1: "a"
    2: "b"
    3: "c"
    _: "d"
check(r == "a")
```

</details>

#### match - middle case

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2
val r = match x:
    1: "a"
    2: "b"
    3: "c"
    _: "d"
check(r == "b")
```

</details>

#### match - last case

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 3
val r = match x:
    1: "a"
    2: "b"
    3: "c"
    _: "d"
check(r == "c")
```

</details>

#### match - default

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 99
val r = match x:
    1: "a"
    2: "b"
    3: "c"
    _: "d"
check(r == "d")
```

</details>

#### match - Some

1. fn run
2. Some
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    val opt = Some(42)
    var r = 0
    match opt:
        Some(x): r = x
        nil: r = -1
    r
check(run() == 42)
```

</details>

#### match - nil

1. fn run
2. Some
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run() -> i64:
    val opt = nil
    var r = 0
    match opt:
        Some(x): r = 99
        nil: r = -1
    r
check(run() == -1)
```

</details>

#### match - boolean true

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = true
val r = match b:
    true: 1
    false: 0
check(r == 1)
```

</details>

#### match - boolean false

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = false
val r = match b:
    true: 1
    false: 0
check(r == 0)
```

</details>

### Array All Branches

#### array - empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = []
check(arr.len() == 0)
```

</details>

#### array - single element

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1]
check(arr.len() == 1)
check(arr[0] == 1)
```

</details>

#### array - multiple elements

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
check(arr.len() == 5)
```

</details>

#### array - index positive

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
check(arr[0] == 10)
check(arr[1] == 20)
check(arr[2] == 30)
```

</details>

#### array - index negative

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
check(arr[-1] == 30)
check(arr[-2] == 20)
check(arr[-3] == 10)
```

</details>

#### array - slice empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
check(slice_len(arr, 1, 1) == 0)
```

</details>

#### array - slice full

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
check(slice_len(arr, 0, 3) == 3)
```

</details>

#### array - slice partial

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3, 4, 5]
check(slice_len(arr, 1, 4) == 3)
```

</details>

### Optional All Branches

#### optional - Some exists

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: i64? = Some(42)
check(opt.?)
```

</details>

#### optional - nil

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: i64? = nil
check(not opt.?)
```

</details>

#### optional - unwrap Some

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
val r = opt ?? 0
check(r == 42)
```

</details>

#### optional - coalesce Some

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
val r = opt ?? 99
check(r == 42)
```

</details>

#### optional - coalesce nil

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt: i64? = nil
val r = opt ?? 99
check(r == 99)
```

</details>

#### optional - chain Some-Some

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(Some(10))
check(opt.?)
```

</details>

#### optional - chain Some-nil

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(nil)
check(opt.?)
```

</details>

#### optional - chain nil

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = nil
check(not opt.?)
```

</details>

### Boolean All Branches

#### and - TT

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((true and true) == true)
```

</details>

#### and - TF

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((true and false) == false)
```

</details>

#### and - FT

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((false and true) == false)
```

</details>

#### and - FF

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((false and false) == false)
```

</details>

#### or - TT

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((true or true) == true)
```

</details>

#### or - TF

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((true or false) == true)
```

</details>

#### or - FT

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((false or true) == true)
```

</details>

#### or - FF

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((false or false) == false)
```

</details>

#### not - T

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((not true) == false)
```

</details>

#### not - F

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((not false) == true)
```

</details>

#### xor - TT

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((true != true) == false)
```

</details>

#### xor - TF

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((true != false) == true)
```

</details>

#### xor - FT

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((false != true) == true)
```

</details>

#### xor - FF

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((false != false) == false)
```

</details>

### Type System All Branches

#### type - int

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64 = 42
check(x == 42)
```

</details>

#### type - float

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: f64 = 3.14
check(x > 3.0)
```

</details>

#### type - bool

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: bool = true
check(x)
```

</details>

#### type - text

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: text = "hello"
check(x == "hello")
```

</details>

#### type - array

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: [i64] = [1, 2, 3]
check(x.len() == 3)
```

</details>

#### type - optional

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x: i64? = Some(42)
check(x.?)
```

</details>

#### type - nil literal

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = nil
check(not x.?)
```

</details>

### Function All Branches

#### function - no params no return

1. fn test
2. test
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test():
    pass
test()
check(true)
```

</details>

#### function - with params

1. fn test
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test(x: i64) -> i64:
    x * 2
check(test(5) == 10)
```

</details>

#### function - multiple params

1. fn test
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test(x: i64, y: i64) -> i64:
    x + y
check(test(3, 4) == 7)
```

</details>

#### function - early return

1. fn test
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test(x: i64) -> i64:
    if x < 0:
        return 0
    x * 2
check(test(-5) == 0)
check(test(5) == 10)
```

</details>

#### function - multiple returns

1. fn test
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn test(x: i64) -> i64:
    if x < 0:
        return -1
    elif x == 0:
        return 0
    else:
        return 1
check(test(-5) == -1)
check(test(0) == 0)
check(test(5) == 1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 81 |
| Active scenarios | 81 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
