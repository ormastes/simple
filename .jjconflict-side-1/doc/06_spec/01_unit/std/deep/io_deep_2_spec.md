# STDLIB Deep-Dive Test

> 1. check

<!-- sdn-diagram:id=io_deep_2_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=io_deep_2_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

io_deep_2_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=io_deep_2_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 43 | 43 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# STDLIB Deep-Dive Test

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #STDLIB-DEEP |
| Category | Standard Library Deep Coverage |
| Status | Implemented |
| Source | `test/01_unit/std/deep/io_deep_2_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Deep Coverage Test

#### basic 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### basic 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(1 == 1)
```

</details>

#### basic 3

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check("a" == "a")
```

</details>

#### op 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

check(1 + 1 == 2)
```

</details>

#### op 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 - 3 == 2)
```

</details>

#### op 3

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(2 * 3 == 6)
```

</details>

#### op 4

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(10 / 2 == 5)
```

</details>

#### op 5

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(10 % 3 == 1)
```

</details>

#### cmp 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

check(5 > 3)
```

</details>

#### cmp 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(3 < 5)
```

</details>

#### cmp 3

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 >= 5)
```

</details>

#### cmp 4

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 <= 5)
```

</details>

#### cmp 5

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(5 != 3)
```

</details>

#### bool 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

check(true and true)
```

</details>

#### bool 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true or false)
```

</details>

#### bool 3

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(not false)
```

</details>

#### arr 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val a = [1,2,3]
check(a.len() == 3)
```

</details>

#### arr 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = []
check(a.len() == 0)
```

</details>

#### arr 3

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1, 2, 3]
check(a.len() == 3)
```

</details>

#### arr 4

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val a = [1,2,3]
check(a.len() == 3)
```

</details>

#### arr 5

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = [1,2]
val b = a.append(3)
check(b.len() == 3)
```

</details>

#### str 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

check("".len() == 0)
```

</details>

#### str 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check("a".len() == 1)
```

</details>

#### str 3

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check("test".len() == 4)
```

</details>

#### str 4

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check("hello".contains("ell"))
```

</details>

#### str 5

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check("test".starts_with("te"))
```

</details>

#### str 6

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check("test".ends_with("st"))
```

</details>

#### opt 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val o = Some(1)
check(o.?)
```

</details>

#### opt 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o = nil
check(not o.?)
```

</details>

#### opt 3

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o = Some(42)
check(o? == 42)
```

</details>

#### opt 4

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val o = nil
check((o ?? 99) == 99)
```

</details>

#### dict 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val d = {"a": 1}
check(d["a"] == 1)
```

</details>

#### dict 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {}
check(true)
```

</details>

#### dict 3

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val d = {"a": 1, "b": 2}
check(d["a"] == 1)
```

</details>

#### if 1

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

#### if 2

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if false:
    check(false)
else:
    check(true)
```

</details>

#### if 3

1. check
2. check


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

#### for 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var c = 0
for i in 0..5:
    c = c + 1
check(c == 5)
```

</details>

#### for 2

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

var s = 0
for i in 0..10:
    s = s + i
check(s == 45)
```

</details>

#### match 1

1. Some
2. nil: check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

match Some(1):
    Some(x): check(x == 1)
    nil: check(false)
```

</details>

#### match 2

1. Some
2. nil: check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

match nil:
    Some(x): check(false)
    nil: check(true)
```

</details>

#### nested 1

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

for i in 0..3:
    for j in 0..3:
        check(true)
```

</details>

#### complex 1

1. evens = evens append
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple

val arr = [1,2,3,4,5]
var evens = []
for x in arr:
    if x % 2 == 0:
        evens = evens.append(x)
check(evens.len() == 2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 43 |
| Active scenarios | 43 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
