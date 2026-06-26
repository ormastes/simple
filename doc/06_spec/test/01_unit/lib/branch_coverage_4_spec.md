# Branch Coverage Test Suite

> Comprehensive branch coverage ensuring every code path is executed. Tests all conditional branches, loops, and match statements.

<!-- sdn-diagram:id=branch_coverage_4_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=branch_coverage_4_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

branch_coverage_4_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=branch_coverage_4_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 78 | 78 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Branch Coverage Test Suite

Comprehensive branch coverage ensuring every code path is executed. Tests all conditional branches, loops, and match statements.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BRANCH |
| Category | Testing |
| Status | Implemented |
| Source | `/home/ormastes/dev/pub/simple/test/01_unit/lib/branch_coverage_4_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Comprehensive branch coverage ensuring every code path is executed.
Tests all conditional branches, loops, and match statements.

## Scenarios

### Conditional Branch Coverage

#### if-then branch taken

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
if x > 5:
    check(true)
else:
    check(false)
```

</details>

#### if-else branch taken

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2
if x > 5:
    check(false)
else:
    check(true)
```

</details>

#### if-elif-then first

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- check
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Some
- nil: check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
match opt:
    Some(x): check(x == 42)
    nil: check(false)
```

</details>

#### match nil

- Some
- nil: check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = nil
match opt:
    Some(x): check(false)
    nil: check(true)
```

</details>

#### match nested Some

- Some
- Some
- nil: check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val nested = Some(Some(10))
match nested:
    Some(Some(x)): check(x == 10)
    Some(nil): check(false)
    nil: check(false)
```

</details>

#### match boolean true

- true: check
- false: check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b = true
match b:
    true: check(true)
    false: check(false)
```

</details>

#### match boolean false

- true: check
- false: check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- fn run for executed
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- fn run for empty
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- fn run for break
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- fn run for continue
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- fn run for all continue
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- fn run while exec
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- fn run while skip
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- fn run while break
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- fn run while continue
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- fn run nested loops
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true and true)
```

</details>

#### and - true/false

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not (true and false))
```

</details>

#### and - false/true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not (false and true))
```

</details>

#### and - false/false

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not (false and false))
```

</details>

#### or - true/true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true or true)
```

</details>

#### or - true/false

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true or false)
```

</details>

#### or - false/true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(false or true)
```

</details>

#### or - false/false

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not (false or false))
```

</details>

#### not - true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not true == false)
```

</details>

#### not - false

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not false == true)
```

</details>

#### complex - (A and B) or C - true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((true and true) or false)
```

</details>

#### complex - (A and B) or C - false then true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check((false and true) or true)
```

</details>

#### complex - A and (B or C) - true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true and (true or false))
```

</details>

#### complex - A and (B or C) - false

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not (false and (true or false)))
```

</details>

### Comparison Branch Coverage

#### equals - true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 == 5)
```

</details>

#### equals - false

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not (5 == 3))
```

</details>

#### not equals - true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 != 3)
```

</details>

#### not equals - false

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not (5 != 5))
```

</details>

#### less than - true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(3 < 5)
```

</details>

#### less than - false

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not (5 < 3))
```

</details>

#### greater than - true

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 > 3)
```

</details>

#### greater than - false

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not (3 > 5))
```

</details>

#### less equal - true equal

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 <= 5)
```

</details>

#### less equal - true less

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(3 <= 5)
```

</details>

#### less equal - false

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not (5 <= 3))
```

</details>

#### greater equal - true equal

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 >= 5)
```

</details>

#### greater equal - true greater

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 >= 3)
```

</details>

#### greater equal - false

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not (3 >= 5))
```

</details>

### Arithmetic Branch Coverage

#### division - positive/positive

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(10 / 2 == 5)
```

</details>

#### division - negative/positive

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(-10 / 2 == -5)
```

</details>

#### division - positive/negative

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(10 / -2 == -5)
```

</details>

#### modulo - positive remainder

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(7 % 3 == 1)
```

</details>

#### modulo - zero remainder

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(6 % 3 == 0)
```

</details>

#### power - positive exponent

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(2 ** 3 == 8)
```

</details>

#### power - zero exponent

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 ** 0 == 1)
```

</details>

### Collection Operation Coverage

#### array index - valid

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
check(arr[0] == 1)
```

</details>

#### array index - negative

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3]
check(arr[-1] == 3)
```

</details>

#### array slice - full range

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
check(arr.len() == 5)
```

</details>

#### array slice - partial

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
check(arr[1..3].len() == 2)
```

</details>

#### array append - to empty

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = []
val result = arr.append(1)
check(result.len() == 1)
```

</details>

#### array append - to non-empty

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2]
val result = arr.append(3)
check(result.len() == 3)
```

</details>

#### dict get - exists

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"key": "value"}
check(d.get("key").?)
```

</details>

#### dict get - missing

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"key": "value"}
check(not d.get("missing").?)
```

</details>

### Option Type Coverage

#### option is some

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
check(opt.?)
```

</details>

#### option is nil

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = nil
check(not opt.?)
```

</details>

#### option unwrap some

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
check(opt? == 42)
```

</details>

#### option chain - some/some

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt1 = Some(Some(10))
check(opt1.?)
```

</details>

#### option coalesce - some

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
val result = opt ?? 0
check(result == 42)
```

</details>

#### option coalesce - nil

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = nil
val result = opt ?? 99
check(result == 99)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 78 |
| Active scenarios | 78 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
