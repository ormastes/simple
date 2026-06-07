# Comprehensive Coverage Test

> 1. check

<!-- sdn-diagram:id=auto_comprehensive_17_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=auto_comprehensive_17_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

auto_comprehensive_17_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=auto_comprehensive_17_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Comprehensive Coverage Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #AUTO |
| Category | Testing |
| Status | Implemented |
| Source | `test/01_unit/lib/common/auto_comprehensive_17_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Comprehensive Test Suite

#### arithmetic coverage 1

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(1 + 1 == 2)
check(5 - 3 == 2)
check(4 * 3 == 12)
check(10 / 2 == 5)
```

</details>

#### arithmetic coverage 2

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(7 % 3 == 1)
check(2 ** 3 == 8)
check(-5 * 2 == -10)
```

</details>

#### comparison coverage 1

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 > 3)
check(2 < 10)
check(5 >= 5)
check(3 <= 3)
```

</details>

#### comparison coverage 2

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(10 != 5)
check(5 == 5)
check(not (3 > 5))
```

</details>

#### boolean logic 1

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true and true)
check(not (true and false))
check(true or false)
check(not (false and false))
```

</details>

#### boolean logic 2

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not false)
check(not not true)
```

</details>

#### string coverage 1

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
check(s.len() == 5)
check(s.contains("ell"))
check(s.starts_with("hel"))
check(s.ends_with("llo"))
```

</details>

#### string coverage 2

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "test"
check(s[0..2] == "te")
check(s + "ing" == "testing")
```

</details>

#### array coverage 1

1. check
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2, 3, 4, 5]
check(arr.len() == 5)
check(arr[0] == 1)
check(arr[4] == 5)
check(arr[-1] == 5)
```

</details>

#### array coverage 2

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [10, 20, 30]
check(arr[0..2].len() == 2)
val appended = arr.append(40)
check(appended.len() == 4)
```

</details>

#### dict coverage 1

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"a": 1, "b": 2}
check(d["a"] == 1)
check(d["b"] == 2)
check(dict_keys(d).len() == 2)
```

</details>

#### dict coverage 2

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"key": "value"}
check(d.get("key").? == true)
check(d.get("missing").? == false)
```

</details>

#### option coverage 1

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val opt = Some(42)
check(opt.?)
check(opt? == 42)
```

</details>

#### option coverage 2

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

#### range coverage 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for i in 0..10:
    count = count + 1
check(count == 10)
```

</details>

#### range coverage 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 1..6:
    sum = sum + i
check(sum == 15)
```

</details>

#### conditional coverage 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val result = if x > 5: "big" else: "small"
check(result == "big")
```

</details>

#### conditional coverage 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 2
val result = if x > 5: "big" else: "small"
check(result == "small")
```

</details>

#### match coverage 1

1. Some
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = Some(100)
val result = match x:
    Some(v): v * 2
    nil: 0
check(result == 200)
```

</details>

#### match coverage 2

1. Some
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = nil
val result = match x:
    Some(v): v * 2
    nil: -1
check(result == -1)
```

</details>

<details>
<summary>Advanced: loop coverage 1</summary>

#### loop coverage 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var total = 0
for i in [10, 20, 30]:
    total = total + i
check(total == 60)
```

</details>


</details>

<details>
<summary>Advanced: loop coverage 2</summary>

#### loop coverage 2

1. fn run while
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn run_while() -> i64:
    var i = 0
    while i < 5:
        i = i + 1
    i
check(run_while() == 5)
```

</details>


</details>

#### nested coverage 1

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = true
val b = true
if a:
    if b:
        check(true)
    else:
        check(false)
else:
    check(false)
```

</details>

#### nested coverage 2

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 10
val y = 20
if x < y:
    if y > 15:
        check(true)
    else:
        check(false)
else:
    check(false)
```

</details>

#### complex expression 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = (1 + 2) * (3 + 4)
check(result == 21)
```

</details>

#### complex expression 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = 10
val b = 5
val result = a * 2 + b / 5
check(result == 21)
```

</details>

#### chained comparison

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 5
check(0 < x and x < 10)
```

</details>

#### ternary-like

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 7
val result = if x % 2 == 0: "even" else: "odd"
check(result == "odd")
```

</details>

#### list comprehension simulation

1. evens = evens append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var evens = []
for i in 0..10:
    if i % 2 == 0:
        evens = evens.append(i)
check(evens.len() == 5)
```

</details>

#### error path

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var error = nil
check(error == nil)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
