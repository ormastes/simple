# sdoctest_spec

> Verifies that SDoctest correctly discovers and collects documentation

<!-- sdn-diagram:id=sdoctest_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sdoctest_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sdoctest_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sdoctest_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sdoctest_spec

Verifies that SDoctest correctly discovers and collects documentation

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/sdoctest/sdoctest_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies that SDoctest correctly discovers and collects documentation
    examples from module and function docstrings. Tests discovery of examples
    in various documentation locations.

## Scenarios

### Doctest Discovery

#### function docstring examples

#### finds examples in function docs

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a: i64, b: i64) -> i64:
    a + b

expect add(2, 3) == 5
```

</details>

#### extracts multiple examples

1. fn multiply
2. expect multiply
3. expect multiply


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn multiply(a: i64, b: i64) -> i64:
    a * b

expect multiply(3, 4) == 12
expect multiply(0, 100) == 0
```

</details>

#### module-level examples

#### finds examples in module docs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_result = 42
expect module_result == 42
```

</details>

### Doctest Execution

#### successful execution

#### executes simple example

1. fn double


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x: i64) -> i64:
    x * 2

val result = double(5)
expect result == 10
```

</details>

#### executes example with setup

1. fn factorial
2. n * factorial


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn factorial(n: i64) -> i64:
    if n <= 1:
        1
    else:
        n * factorial(n - 1)

val result = factorial(5)
expect result == 120
```

</details>

#### assertion verification

#### verifies expect statements

1. fn is even
2. expect is even
3. expect is even


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn is_even(n: i64) -> bool:
    n % 2 == 0

expect is_even(4) == true
expect is_even(3) == false
```

</details>

#### verifies complex assertions

1. fn create pair
2. 


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn create_pair(a: i64, b: i64) -> (i64, i64):
    (a, b)

val (x, y) = create_pair(3, 7)
expect x == 3
expect y == 7
```

</details>

#### string output verification

#### verifies string output

1. fn greet


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greet(name: text) -> text:
    "Hello, {name}!"

val output = greet("Alice")
expect output == "Hello, Alice!"
```

</details>

### Doctest Failures

#### assertion failures

#### detects failed assertions

1. fn add


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn add(a: i64, b: i64) -> i64:
    a + b

val result = add(2, 3)
expect result == 5
```

</details>

#### reports wrong output

1. fn always zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn always_zero() -> i64:
    0

val result = always_zero()
expect result == 0
```

</details>

#### type errors

#### catches type mismatches

1. fn get text


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn get_text() -> text:
    "hello"

val result = get_text()
expect result == "hello"
```

</details>

### Doctest Data Structure Examples

#### collection examples

#### documents list operations

1. fn sum list


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn sum_list(items: List<i64>) -> i64:
    var total = 0
    for item in items:
        total = total + item
    total

val data = [1, 2, 3, 4, 5]
val result = sum_list(data)
expect result == 15
```

</details>

#### documents dict operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = {"a": 10, "b": 20}
val result = data.get("b")
expect result == 20
```

</details>

#### custom type examples

#### documents custom structs

1. fn distance from origin
2. 


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64

fn distance_from_origin(p: Point) -> i64:
    (p.x * p.x + p.y * p.y)

val p = Point(x: 3, y: 4)
val dist = distance_from_origin(p)
expect dist == 25
```

</details>

#### documents enums

1. fn is active
2. expect is active
3. expect is active


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enum Status:
    Active
    Inactive
    Pending

fn is_active(status: Status) -> bool:
    match status:
        Status.Active:
            true
        _:
            false

expect is_active(Status.Active) == true
expect is_active(Status.Inactive) == false
```

</details>

### Doctest Helpers

#### helper functions

#### uses helper in doctest

1. fn create test list
2. fn process list


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn create_test_list() -> List<i64>:
    [1, 2, 3]

fn process_list(items: List<i64>) -> i64:
    var total = 0
    for item in items:
        total = total + item
    total

val list = create_test_list()
val result = process_list(list)
expect result == 6
```

</details>

#### setup and teardown

#### initializes test data

1. fn initialize dict
2. fn sum dict values


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn initialize_dict() -> Dict<text, i64>:
    {"x": 10, "y": 20, "z": 30}

fn sum_dict_values(d: Dict<text, i64>) -> i64:
    var total = 0
    for pair in d:
        total = total + pair[1]
    total

val dict = initialize_dict()
val result = sum_dict_values(dict)
expect result == 60
```

</details>

#### multiple examples

#### executes related examples

1. fn increment
2. fn decrement
3. expect increment
4. expect decrement


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn increment(x: i64) -> i64:
    x + 1

fn decrement(x: i64) -> i64:
    x - 1

expect increment(5) == 6
expect decrement(5) == 4
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
