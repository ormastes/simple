# Branch Coverage 27 Specification

> Tests covering Lexer All Branches, Parser All Branches, Control Flow All Branches, Loop All Branches, Match All Branches, Array All Branches, Optional All Branches, Boolean All Branches, Type System All Branches, Function All Branches.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 81 | 81 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Branch Coverage 27 Specification

## Scenarios

### Lexer All Branches

#### handles all numeric formats

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- handles all numeric formats


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles all numeric formats")
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

- handles all float formats


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles all float formats")
val normal = 3.14
val exp_pos = 1.5e10
val exp_neg = 2.5e-5
check(normal > 3.0)
check(exp_pos > 1.0)
check(exp_neg < 1.0)
```

</details>

#### handles all string escapes

- handles all string escapes


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles all string escapes")
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

- handles raw strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles raw strings")
val raw = r"\n\t\\"
check(raw.contains("\\"))
```

</details>

#### handles multiline strings

- handles multiline strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles multiline strings")
val multi = """
line 1
line 2
"""
check(multi.contains("line"))
```

</details>

#### handles string interpolation - all cases

- handles string interpolation - all cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles string interpolation - all cases")
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

- handles all operators - arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles all operators - arithmetic")
check(2 + 3 == 5)
check(5 - 2 == 3)
check(3 * 4 == 12)
check(10 / 2 == 5)
check(10 % 3 == 1)
check(2 ** 3 == 8)
```

</details>

#### handles all operators - comparison

- handles all operators - comparison


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles all operators - comparison")
check(5 == 5)
check(5 != 4)
check(5 > 4)
check(5 >= 5)
check(4 < 5)
check(4 <= 4)
```

</details>

#### handles all operators - logical

- handles all operators - logical


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles all operators - logical")
check(true and true)
check(true or false)
check(not false)
```

</details>

#### handles all operators - bitwise

- handles all operators - bitwise


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles all operators - bitwise")
check((5 & 3) == 1)
check((5 | 3) == 7)
check((5 ^ 3) == 6)
```

</details>

#### handles unary operators

- handles unary operators


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles unary operators")
check(-5 < 0)
check(5 > 0)
check(not false == true)
```

</details>

#### handles precedence - all levels

- handles precedence - all levels


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles precedence - all levels")
check(2 + 3 * 4 == 14)
check((2 + 3) * 4 == 20)
check(2 ** 3 * 4 == 32)
check(10 - 5 - 2 == 3)
```

</details>

#### handles associativity

- handles associativity


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles associativity")
check(10 - 5 - 2 == 3)
check(2 ** 3 ** 2 == 512)
```

</details>

### Control Flow All Branches

#### if - then only

- if - then only


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("if - then only")
fn run() -> i64:
    var x = 0
    if true:
        x = 1
    x
check(run() == 1)
```

</details>

#### if - else taken

- if - else taken


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("if - else taken")
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

- if - elif - first


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("if - elif - first")
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

- if - elif - second


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("if - elif - second")
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

- if - elif - else


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("if - elif - else")
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

- nested if - all paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested if - all paths")
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

- for - empty range


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for - empty range")
fn run() -> i64:
    var count = 0
    for i in 0..0:
        count = count + 1
    count
check(run() == 0)
```

</details>

#### for - single iteration

- for - single iteration


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for - single iteration")
fn run() -> i64:
    var count = 0
    for i in 0..1:
        count = count + 1
    count
check(run() == 1)
```

</details>

#### for - multiple iterations

- for - multiple iterations


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for - multiple iterations")
fn run() -> i64:
    var count = 0
    for i in 0..5:
        count = count + 1
    count
check(run() == 5)
```

</details>

#### for - with break first

- for - with break first


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for - with break first")
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

- for - with break middle


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for - with break middle")
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

- for - with continue


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for - with continue")
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

- for - all continue


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for - all continue")
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

- while - never enters


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("while - never enters")
fn run() -> i64:
    var count = 0
    while false:
        count = count + 1
    count
check(run() == 0)
```

</details>

#### while - enters once

- while - enters once


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("while - enters once")
fn run() -> i64:
    var count = 0
    while count < 1:
        count = count + 1
    count
check(run() == 1)
```

</details>

#### while - multiple times

- while - multiple times


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("while - multiple times")
fn run() -> i64:
    var count = 0
    while count < 5:
        count = count + 1
    count
check(run() == 5)
```

</details>

#### while - with break

- while - with break


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("while - with break")
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

- while - with continue


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("while - with continue")
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

- match - first case


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match - first case")
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

- match - middle case


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match - middle case")
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

- match - last case


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match - last case")
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

- match - default


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match - default")
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

- match - Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match - Some")
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

- match - nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match - nil")
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

- match - boolean true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match - boolean true")
val b = true
val r = match b:
    true: 1
    false: 0
check(r == 1)
```

</details>

#### match - boolean false

- match - boolean false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match - boolean false")
val b = false
val r = match b:
    true: 1
    false: 0
check(r == 0)
```

</details>

### Array All Branches

#### array - empty

- array - empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array - empty")
val arr = []
check(arr.len() == 0)
```

</details>

#### array - single element

- array - single element


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array - single element")
val arr = [1]
check(arr.len() == 1)
check(arr[0] == 1)
```

</details>

#### array - multiple elements

- array - multiple elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array - multiple elements")
val arr = [1, 2, 3, 4, 5]
check(arr.len() == 5)
```

</details>

#### array - index positive

- array - index positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array - index positive")
val arr = [10, 20, 30]
check(arr[0] == 10)
check(arr[1] == 20)
check(arr[2] == 30)
```

</details>

#### array - index negative

- array - index negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array - index negative")
val arr = [10, 20, 30]
check(arr[-1] == 30)
check(arr[-2] == 20)
check(arr[-3] == 10)
```

</details>

#### array - slice empty

- array - slice empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array - slice empty")
val arr = [1, 2, 3]
check(slice_len(arr, 1, 1) == 0)
```

</details>

#### array - slice full

- array - slice full


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array - slice full")
val arr = [1, 2, 3]
check(slice_len(arr, 0, 3) == 3)
```

</details>

#### array - slice partial

- array - slice partial


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array - slice partial")
val arr = [1, 2, 3, 4, 5]
check(slice_len(arr, 1, 4) == 3)
```

</details>

### Optional All Branches

#### optional - Some exists

- optional - Some exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional - Some exists")
val opt: i64? = Some(42)
check(opt.?)
```

</details>

#### optional - nil

- optional - nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional - nil")
val opt: i64? = nil
check(not opt.?)
```

</details>

#### optional - unwrap Some

- optional - unwrap Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional - unwrap Some")
val opt = Some(42)
val r = opt ?? 0
check(r == 42)
```

</details>

#### optional - coalesce Some

- optional - coalesce Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional - coalesce Some")
val opt = Some(42)
val r = opt ?? 99
check(r == 42)
```

</details>

#### optional - coalesce nil

- optional - coalesce nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional - coalesce nil")
val opt: i64? = nil
val r = opt ?? 99
check(r == 99)
```

</details>

#### optional - chain Some-Some

- optional - chain Some-Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional - chain Some-Some")
val opt = Some(Some(10))
check(opt.?)
```

</details>

#### optional - chain Some-nil

- optional - chain Some-nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional - chain Some-nil")
val opt = Some(nil)
check(not opt.?)
```

</details>

#### optional - chain nil

- optional - chain nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("optional - chain nil")
val opt = nil
check(not opt.?)
```

</details>

### Boolean All Branches

#### and - TT

- and - TT


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("and - TT")
check((true and true) == true)
```

</details>

#### and - TF

- and - TF


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("and - TF")
check((true and false) == false)
```

</details>

#### and - FT

- and - FT


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("and - FT")
check((false and true) == false)
```

</details>

#### and - FF

- and - FF


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("and - FF")
check((false and false) == false)
```

</details>

#### or - TT

- or - TT


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or - TT")
check((true or true) == true)
```

</details>

#### or - TF

- or - TF


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or - TF")
check((true or false) == true)
```

</details>

#### or - FT

- or - FT


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or - FT")
check((false or true) == true)
```

</details>

#### or - FF

- or - FF


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or - FF")
check((false or false) == false)
```

</details>

#### not - T

- not - T


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("not - T")
check((not true) == false)
```

</details>

#### not - F

- not - F


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("not - F")
check((not false) == true)
```

</details>

#### xor - TT

- xor - TT


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("xor - TT")
check((true != true) == false)
```

</details>

#### xor - TF

- xor - TF


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("xor - TF")
check((true != false) == true)
```

</details>

#### xor - FT

- xor - FT


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("xor - FT")
check((false != true) == true)
```

</details>

#### xor - FF

- xor - FF


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("xor - FF")
check((false != false) == false)
```

</details>

### Type System All Branches

#### type - int

- type - int


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type - int")
val x: i64 = 42
check(x == 42)
```

</details>

#### type - float

- type - float


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type - float")
val x: f64 = 3.14
check(x > 3.0)
```

</details>

#### type - bool

- type - bool


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type - bool")
val x: bool = true
check(x)
```

</details>

#### type - text

- type - text


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type - text")
val x: text = "hello"
check(x == "hello")
```

</details>

#### type - array

- type - array


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type - array")
val x: [i64] = [1, 2, 3]
check(x.len() == 3)
```

</details>

#### type - optional

- type - optional


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type - optional")
val x: i64? = Some(42)
check(x.?)
```

</details>

#### type - nil literal

- type - nil literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type - nil literal")
val x = nil
check(not x.?)
```

</details>

### Function All Branches

#### function - no params no return

- function - no params no return


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function - no params no return")
fn test():
    pass
test()
check(true)
```

</details>

#### function - with params

- function - with params


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function - with params")
fn test(x: i64) -> i64:
    x * 2
check(test(5) == 10)
```

</details>

#### function - multiple params

- function - multiple params


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function - multiple params")
fn test(x: i64, y: i64) -> i64:
    x + y
check(test(3, 4) == 7)
```

</details>

#### function - early return

- function - early return


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function - early return")
fn test(x: i64) -> i64:
    if x < 0:
        return 0
    x * 2
check(test(-5) == 0)
check(test(5) == 10)
```

</details>

#### function - multiple returns

- function - multiple returns


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function - multiple returns")
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

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler_core/branch_coverage_27_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Lexer All Branches, Parser All Branches, Control Flow All Branches, Loop All Branches, Match All Branches, Array All Branches, Optional All Branches, Boolean All Branches, Type System All Branches, Function All Branches.
- Lexer All Branches
- Parser All Branches
- Control Flow All Branches
- Loop All Branches
- Match All Branches
- Array All Branches
- Optional All Branches
- Boolean All Branches
- Type System All Branches
- Function All Branches

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 81 |
| Active scenarios | 81 |
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

- Canonical SPipe generation for source `be234780dc1ffde464767716aa6fa73a5a240705f06b0aa0fff623718132065f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `be234780dc1ffde464767716aa6fa73a5a240705f06b0aa0fff623718132065f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `be234780dc1ffde464767716aa6fa73a5a240705f06b0aa0fff623718132065f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler_core/branch_coverage_27_spec.spl
mirror: doc/06_spec/unit/compiler_core/branch_coverage_27_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler_core/branch_coverage_27_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler_core/branch_coverage_27_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler_core/branch_coverage_27_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles all numeric formats' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/branch_coverage_27_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles all float formats' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler_core/branch_coverage_27_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles all string escapes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
