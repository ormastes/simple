# Branch Coverage 3 Specification

> Tests covering Conditional Branch Coverage, Match Statement Coverage, Loop Branch Coverage, Boolean Expression Coverage, Comparison Branch Coverage, Arithmetic Branch Coverage, Collection Operation Coverage, Option Type Coverage.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 78 | 78 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Branch Coverage 3 Specification

## Scenarios

### Conditional Branch Coverage

#### if-then branch taken

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- if-then branch taken


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("if-then branch taken")
val x = 10
if x > 5:
    check(true)
else:
    check(false)
```

</details>

#### if-else branch taken

- if-else branch taken


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("if-else branch taken")
val x = 2
if x > 5:
    check(false)
else:
    check(true)
```

</details>

#### if-elif-then first

- if-elif-then first


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("if-elif-then first")
val x = 15
if x > 10:
    check(true)
elif x > 5:
    check(false)
else:
    check(false)
```

</details>

#### if-elif-then second

- if-elif-then second


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("if-elif-then second")
val x = 7
if x > 10:
    check(false)
else:
    if x > 5:
        check(true)
    else:
        check(false)
```

</details>

#### if-elif-else taken

- if-elif-else taken


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("if-elif-else taken")
val x = 3
if x > 10:
    check(false)
elif x > 5:
    check(false)
else:
    check(true)
```

</details>

#### nested if - true/true

- nested if - true/true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested if - true/true")
if true:
    if true:
        check(true)
    else:
        check(false)
else:
    check(false)
```

</details>

#### nested if - true/false

- nested if - true/false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested if - true/false")
if true:
    if false:
        check(false)
    else:
        check(true)
else:
    check(false)
```

</details>

#### nested if - false/true

- nested if - false/true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested if - false/true")
if false:
    if true:
        check(false)
    else:
        check(false)
else:
    check(true)
```

</details>

#### nested if - false/false

- nested if - false/false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested if - false/false")
if false:
    if false:
        check(false)
    else:
        check(false)
else:
    check(true)
```

</details>

#### triple nested - all true

- triple nested - all true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("triple nested - all true")
if true:
    if true:
        if true:
            check(true)
        else:
            check(false)
    else:
        check(false)
else:
    check(false)
```

</details>

### Match Statement Coverage

#### match - pattern 1

- match - pattern 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match - pattern 1")
val x = 1
val result = match x:
    1: "one"
    2: "two"
    3: "three"
    _: "other"
check(result == "one")
```

</details>

#### match - pattern 2

- match - pattern 2


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match - pattern 2")
val x = 2
val result = match x:
    1: "one"
    2: "two"
    3: "three"
    _: "other"
check(result == "two")
```

</details>

#### match - pattern 3

- match - pattern 3


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match - pattern 3")
val x = 3
val result = match x:
    1: "one"
    2: "two"
    3: "three"
    _: "other"
check(result == "three")
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
val result = match x:
    1: "one"
    2: "two"
    3: "three"
    _: "other"
check(result == "other")
```

</details>

#### match Some

- match Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match Some")
val opt = Some(42)
match opt:
    Some(x): check(x == 42)
    nil: check(false)
```

</details>

#### match nil

- match nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match nil")
val opt = nil
match opt:
    Some(x): check(false)
    nil: check(true)
```

</details>

#### match nested Some

- match nested Some


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match nested Some")
val nested = Some(Some(10))
match nested:
    Some(Some(x)): check(x == 10)
    Some(nil): check(false)
    nil: check(false)
```

</details>

#### match boolean true

- match boolean true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match boolean true")
val b = true
match b:
    true: check(true)
    false: check(false)
```

</details>

#### match boolean false

- match boolean false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match boolean false")
val b = false
match b:
    true: check(false)
    false: check(true)
```

</details>

### Loop Branch Coverage

<details>
<summary>Advanced: for loop - executed</summary>

#### for loop - executed

- for loop - executed


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for loop - executed")
fn run_for_executed() -> i64:
    var count = 0
    for i in 0..10:
        count = count + 1
    count
check(run_for_executed() == 10)
```

</details>


</details>

<details>
<summary>Advanced: for loop - empty range</summary>

#### for loop - empty range

- for loop - empty range


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for loop - empty range")
fn run_for_empty() -> i64:
    var count = 0
    for i in 0..0:
        count = count + 1
    count
check(run_for_empty() == 0)
```

</details>


</details>

<details>
<summary>Advanced: for loop - with break</summary>

#### for loop - with break

- for loop - with break


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for loop - with break")
fn run_for_break() -> i64:
    var count = 0
    for i in 0..100:
        count = count + 1
        if count == 5:
            break
    count
check(run_for_break() == 5)
```

</details>


</details>

<details>
<summary>Advanced: for loop - with continue</summary>

#### for loop - with continue

- for loop - with continue


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for loop - with continue")
fn run_for_continue() -> i64:
    var count = 0
    for i in 0..10:
        if i % 2 == 0:
            continue
        count = count + 1
    count
check(run_for_continue() == 5)
```

</details>


</details>

<details>
<summary>Advanced: for loop - all continue</summary>

#### for loop - all continue

- for loop - all continue


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("for loop - all continue")
fn run_for_all_continue() -> i64:
    var count = 0
    for i in 0..10:
        continue
        count = count + 1  # Never reached
    count
check(run_for_all_continue() == 0)
```

</details>


</details>

<details>
<summary>Advanced: while loop - executed</summary>

#### while loop - executed

- while loop - executed


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("while loop - executed")
fn run_while_exec() -> i64:
    var count = 0
    while count < 5:
        count = count + 1
    count
check(run_while_exec() == 5)
```

</details>


</details>

<details>
<summary>Advanced: while loop - not executed</summary>

#### while loop - not executed

- while loop - not executed


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("while loop - not executed")
fn run_while_skip() -> i64:
    var count = 10
    while count < 5:
        count = count + 1
    count
check(run_while_skip() == 10)
```

</details>


</details>

<details>
<summary>Advanced: while loop - with break</summary>

#### while loop - with break

- while loop - with break


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("while loop - with break")
fn run_while_break() -> i64:
    var count = 0
    while true:
        count = count + 1
        if count == 3:
            break
    count
check(run_while_break() == 3)
```

</details>


</details>

<details>
<summary>Advanced: while loop - with continue</summary>

#### while loop - with continue

- while loop - with continue


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("while loop - with continue")
fn run_while_continue() -> i64:
    var count = 0
    var iterations = 0
    while count < 10:
        count = count + 1
        if count % 2 == 0:
            continue
        iterations = iterations + 1
    iterations
check(run_while_continue() == 5)
```

</details>


</details>

<details>
<summary>Advanced: nested loops - both execute</summary>

#### nested loops - both execute

- nested loops - both execute


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("nested loops - both execute")
fn run_nested_loops() -> i64:
    var total = 0
    for i in 0..3:
        for j in 0..3:
            total = total + 1
    total
check(run_nested_loops() == 9)
```

</details>


</details>

### Boolean Expression Coverage

#### and - true/true

- and - true/true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("and - true/true")
check(true and true)
```

</details>

#### and - true/false

- and - true/false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("and - true/false")
check(not (true and false))
```

</details>

#### and - false/true

- and - false/true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("and - false/true")
check(not (false and true))
```

</details>

#### and - false/false

- and - false/false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("and - false/false")
check(not (false and false))
```

</details>

#### or - true/true

- or - true/true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or - true/true")
check(true or true)
```

</details>

#### or - true/false

- or - true/false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or - true/false")
check(true or false)
```

</details>

#### or - false/true

- or - false/true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or - false/true")
check(false or true)
```

</details>

#### or - false/false

- or - false/false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("or - false/false")
check(not (false or false))
```

</details>

#### not - true

- not - true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("not - true")
check(not true == false)
```

</details>

#### not - false

- not - false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("not - false")
check(not false == true)
```

</details>

#### complex - (A and B) or C - true

- complex - (A and B) or C - true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("complex - (A and B) or C - true")
check((true and true) or false)
```

</details>

#### complex - (A and B) or C - false then true

- complex - (A and B) or C - false then true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("complex - (A and B) or C - false then true")
check((false and true) or true)
```

</details>

#### complex - A and (B or C) - true

- complex - A and (B or C) - true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("complex - A and (B or C) - true")
check(true and (true or false))
```

</details>

#### complex - A and (B or C) - false

- complex - A and (B or C) - false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("complex - A and (B or C) - false")
check(not (false and (true or false)))
```

</details>

### Comparison Branch Coverage

#### equals - true

- equals - true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("equals - true")
check(5 == 5)
```

</details>

#### equals - false

- equals - false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("equals - false")
check(not (5 == 3))
```

</details>

#### not equals - true

- not equals - true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("not equals - true")
check(5 != 3)
```

</details>

#### not equals - false

- not equals - false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("not equals - false")
check(not (5 != 5))
```

</details>

#### less than - true

- less than - true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("less than - true")
check(3 < 5)
```

</details>

#### less than - false

- less than - false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("less than - false")
check(not (5 < 3))
```

</details>

#### greater than - true

- greater than - true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("greater than - true")
check(5 > 3)
```

</details>

#### greater than - false

- greater than - false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("greater than - false")
check(not (3 > 5))
```

</details>

#### less equal - true equal

- less equal - true equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("less equal - true equal")
check(5 <= 5)
```

</details>

#### less equal - true less

- less equal - true less


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("less equal - true less")
check(3 <= 5)
```

</details>

#### less equal - false

- less equal - false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("less equal - false")
check(not (5 <= 3))
```

</details>

#### greater equal - true equal

- greater equal - true equal


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("greater equal - true equal")
check(5 >= 5)
```

</details>

#### greater equal - true greater

- greater equal - true greater


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("greater equal - true greater")
check(5 >= 3)
```

</details>

#### greater equal - false

- greater equal - false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("greater equal - false")
check(not (3 >= 5))
```

</details>

### Arithmetic Branch Coverage

#### division - positive/positive

- division - positive/positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("division - positive/positive")
check(10 / 2 == 5)
```

</details>

#### division - negative/positive

- division - negative/positive


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("division - negative/positive")
check(-10 / 2 == -5)
```

</details>

#### division - positive/negative

- division - positive/negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("division - positive/negative")
check(10 / -2 == -5)
```

</details>

#### modulo - positive remainder

- modulo - positive remainder


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("modulo - positive remainder")
check(7 % 3 == 1)
```

</details>

#### modulo - zero remainder

- modulo - zero remainder


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("modulo - zero remainder")
check(6 % 3 == 0)
```

</details>

#### power - positive exponent

- power - positive exponent


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("power - positive exponent")
check(2 ** 3 == 8)
```

</details>

#### power - zero exponent

- power - zero exponent


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("power - zero exponent")
check(5 ** 0 == 1)
```

</details>

### Collection Operation Coverage

#### array index - valid

- array index - valid


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array index - valid")
var arr = [1, 2, 3]
check(arr[0] == 1)
```

</details>

#### array index - negative

- array index - negative


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array index - negative")
var arr = [1, 2, 3]
check(arr[-1] == 3)
```

</details>

#### array slice - full range

- array slice - full range


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array slice - full range")
var arr = [1, 2, 3, 4, 5]
check(arr.len() == 5)
```

</details>

#### array slice - partial

- array slice - partial


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array slice - partial")
var arr = [1, 2, 3, 4, 5]
check(arr[1..3].len() == 2)
```

</details>

#### array append - to empty

- array append - to empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array append - to empty")
var arr = []
val result = arr.append(1)
check(result.len() == 1)
```

</details>

#### array append - to non-empty

- array append - to non-empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("array append - to non-empty")
var arr = [1, 2]
val result = arr.append(3)
check(result.len() == 3)
```

</details>

#### dict get - exists

- dict get - exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dict get - exists")
val d = {"key": "value"}
check(d.get("key") != nil)
```

</details>

#### dict get - missing

- dict get - missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("dict get - missing")
val d = {"key": "value"}
check(not d.get("missing").?)
```

</details>

### Option Type Coverage

#### option is some

- option is some


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("option is some")
val opt = Some(42)
check(opt != nil)
```

</details>

#### option is nil

- option is nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("option is nil")
val opt = nil
check(not opt.?)
```

</details>

#### option unwrap some

- option unwrap some


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("option unwrap some")
val opt = Some(42)
check(opt? == 42)
```

</details>

#### option chain - some/some

- option chain - some/some


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("option chain - some/some")
val opt1 = Some(Some(10))
check(opt1 != nil)
```

</details>

#### option coalesce - some

- option coalesce - some


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("option coalesce - some")
val opt = Some(42)
val result = opt ?? 0
check(result == 42)
```

</details>

#### option coalesce - nil

- option coalesce - nil


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("option coalesce - nil")
val opt = nil
val result = opt ?? 99
check(result == 99)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/branch_coverage_3_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Conditional Branch Coverage, Match Statement Coverage, Loop Branch Coverage, Boolean Expression Coverage, Comparison Branch Coverage, Arithmetic Branch Coverage, Collection Operation Coverage, Option Type Coverage.
- Conditional Branch Coverage
- Match Statement Coverage
- Loop Branch Coverage
- Boolean Expression Coverage
- Comparison Branch Coverage
- Arithmetic Branch Coverage
- Collection Operation Coverage
- Option Type Coverage

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 78 |
| Active scenarios | 78 |
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

- Canonical SPipe generation for source `6dd039ccc57d2477a5cba13b14447418680fd68aba57f8f03c0699bae052a475`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6dd039ccc57d2477a5cba13b14447418680fd68aba57f8f03c0699bae052a475`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6dd039ccc57d2477a5cba13b14447418680fd68aba57f8f03c0699bae052a475`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/branch_coverage_3_spec.spl
mirror: doc/06_spec/unit/app/branch_coverage_3_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/branch_coverage_3_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/branch_coverage_3_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/branch_coverage_3_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'if-then branch taken' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/branch_coverage_3_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'if-else branch taken' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/branch_coverage_3_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'if-elif-then first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
