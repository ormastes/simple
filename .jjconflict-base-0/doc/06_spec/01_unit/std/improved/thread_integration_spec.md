# STDLIB Module Comprehensive Test

> 1. check

<!-- sdn-diagram:id=thread_integration_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=thread_integration_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

thread_integration_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=thread_integration_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 41 | 41 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# STDLIB Module Comprehensive Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #STDLIB |
| Category | Standard Library |
| Status | Implemented |
| Source | `test/01_unit/std/improved/thread_integration_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### STDLIB Module Complete Test

#### basic operation 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(1 + 1 == 2)
```

</details>

#### basic operation 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val x = "test"
check(x.len() == 4)
```

</details>

#### basic operation 3

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val arr = [1, 2, 3]
check(arr.len() == 3)
```

</details>

#### type conversion 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val s = "42"
check(s.len() == 2)
```

</details>

#### type conversion 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val num = 42
check(num > 0)
```

</details>

#### collection operations 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val arr = [1, 2, 3, 4, 5]
var sum = 0
for x in arr:
    sum = sum + x
check(sum == 15)
```

</details>

#### collection operations 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var arr = [1, 2, 3]
val result = arr.append(4)
check(result.len() == 4)
```

</details>

#### collection operations 3

1. evens = evens append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val arr = [1, 2, 3, 4, 5]
var evens = []
for x in arr:
    if x % 2 == 0:
        evens = evens.append(x)
check(evens.len() == 2)
```

</details>

#### string operations 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val s = "hello"
check(s.starts_with("hel"))
```

</details>

#### string operations 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val s = "world"
check(s.ends_with("rld"))
```

</details>

#### string operations 3

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val s = "test string"
check(s.contains("str"))
```

</details>

#### option handling 1

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val opt = Some(42)
check(opt.?)
check(opt? == 42)
```

</details>

#### option handling 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val opt = nil
check(not opt.?)
```

</details>

#### option handling 3

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val opt = Some(100)
val result = opt ?? 0
check(result == 100)
```

</details>

#### option handling 4

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val opt = nil
val result = opt ?? 99
check(result == 99)
```

</details>

#### error path 1

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val opt = nil
if opt.?:
    check(false)
else:
    check(true)
```

</details>

#### error path 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val arr = []
check(arr.len() == 0)
```

</details>

#### error path 3

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var error = nil
check(error == nil)
```

</details>

#### edge case 1 - empty

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val s = ""
check(s.len() == 0)
```

</details>

#### edge case 2 - zero

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

check(0 == 0)
check(not (0 > 0))
```

</details>

#### edge case 3 - negative

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

check(-1 < 0)
```

</details>

#### edge case 4 - large

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

check(999999 > 0)
```

</details>

#### edge case 5 - single element

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val arr = [1]
check(arr.len() == 1)
```

</details>

#### boundary 1 - min

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val arr = [1, 2, 3]
check(arr.len() == 3)
```

</details>

#### boundary 2 - max

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val arr = [1, 2, 3]
check(arr.len() == 3)
```

</details>

#### conditional 1

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

if true:
    check(true)
else:
    check(false)
```

</details>

#### conditional 2

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val x = 10
if x > 5:
    check(true)
else:
    check(false)
```

</details>

#### conditional 3

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
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

<details>
<summary>Advanced: loop 1 - for</summary>

#### loop 1 - for

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var count = 0
for i in 0..10:
    count = count + 1
check(count == 10)
```

</details>


</details>

<details>
<summary>Advanced: loop 2 - while</summary>

#### loop 2 - while

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var count = 0
while count < 5:
    count = count + 1
check(count == 5)
```

</details>


</details>

<details>
<summary>Advanced: loop 3 - break</summary>

#### loop 3 - break

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var count = 0
for i in 0..100:
    count = count + 1
    if count == 5:
        break
check(count == 5)
```

</details>


</details>

<details>
<summary>Advanced: loop 4 - continue</summary>

#### loop 4 - continue

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var executed = 0
for i in 0..10:
    if i % 2 == 0:
        continue
    executed = executed + 1
check(executed == 5)
```

</details>


</details>

#### match 1

1. Some
2. nil: check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val opt = Some(1)
match opt:
    Some(x): check(x == 1)
    nil: check(false)
```

</details>

#### match 2

1. Some
2. nil: check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val opt = nil
match opt:
    Some(x): check(false)
    nil: check(true)
```

</details>

#### match 3

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val value = 2
val result = match value:
    1: "one"
    2: "two"
    3: "three"
    _: "other"
check(result == "two")
```

</details>

#### nested 1

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
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

#### nested 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

for i in 0..3:
    for j in 0..3:
        check(i >= 0 and j >= 0)
```

</details>

#### complex 1

1. result = result append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val arr = [1, 2, 3, 4, 5]
var result = []
for x in arr:
    if x % 2 == 0:
        result = result.append(x * 2)
check(result.len() == 2)
```

</details>

#### complex 2

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val dict = {"a": 1, "b": 2, "c": 3}
check(dict["a"] == 1)
check(dict["b"] == 2)
check(dict["c"] == 3)
```

</details>

#### integration 1

1. processed = processed append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val data = [1, 2, 3]
var processed = []
for x in data:
    processed = processed.append(x * 2)
var sum = 0
for x in processed:
    sum = sum + x
check(sum == 12)
```

</details>

#### integration 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val input = "test"
val stage1 = input + "_1"
val stage2 = stage1 + "_2"
val stage3 = stage2 + "_3"
check(stage3 == "test_1_2_3")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 41 |
| Active scenarios | 41 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
