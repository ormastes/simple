# Lifetime Analysis Unit Tests

> <details>

<!-- sdn-diagram:id=lifetime_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=lifetime_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

lifetime_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=lifetime_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lifetime Analysis Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COMPILER-BORROW-002 |
| Category | Compiler \| Borrow \| Lifetime |
| Status | Implemented |
| Source | `test/01_unit/compiler/borrow/lifetime_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Variable Lifetimes

#### lifetime starts at declaration

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
check(x == 42)
```

</details>

#### lifetime ends at scope exit

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = 0
if true:
    val temp = 42
    result = temp
check(result == 42)
```

</details>

#### nested lifetimes

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val outer = 1
if true:
    val middle = 2
    if true:
        val inner = 3
        check(outer + middle + inner == 6)
```

</details>

<details>
<summary>Advanced: loop variable lifetime per iteration</summary>

#### loop variable lifetime per iteration

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sum = 0
for i in 0..3:
    val temp = i * 10
    sum = sum + temp
check(sum == 30)
```

</details>


</details>

#### match arm lifetimes

- Some
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = Some(42)
var result = 0
match x:
    Some(v):
        val doubled = v * 2
        result = doubled
    nil:
        result = 0
check(result == 84)
```

</details>

### Reference Lifetimes

#### reference lives within function

- fn get value
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_value() -> i64:
    val x = 42
    x
check(get_value() == 42)
```

</details>

#### return value outlives function

- fn create
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn create() -> i64:
    42
val result = create()
check(result == 42)
```

</details>

#### closure captures extend lifetime

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = 42
val f = \: x
check(f() == 42)
```

</details>

#### array element lifetime

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [10, 20, 30]
val first = arr[0]
check(first == 10)
```

</details>

### Drop Ordering

#### LIFO drop order

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val first = 1
val second = 2
val third = 3
check(first + second + third == 6)
```

</details>

#### struct fields drop with struct

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Pair:
    a: i64
    b: i64
val p = Pair(a: 1, b: 2)
check(p.a + p.b == 3)
```

</details>

#### array elements drop with array

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arr = [1, 2, 3]
check(arr.len() == 3)
```

</details>

### Temporary Lifetimes

#### temporary in expression

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = [1, 2, 3].len()
check(result == 3)
```

</details>

#### temporary in function call

- fn sum len
- arr len
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn sum_len(arr: [i64]) -> i64:
    arr.len()
check(sum_len([1, 2, 3]) == 3)
```

</details>

#### chained temporaries

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = "hello world".len()
check(result == 11)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
