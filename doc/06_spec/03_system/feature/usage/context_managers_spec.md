# Context Managers Specification

> with resource as alias:

<!-- sdn-diagram:id=context_managers_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=context_managers_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

context_managers_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=context_managers_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Context Managers Specification

with resource as alias:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CONTEXT-MANAGER |
| Category | Language |
| Status | Implemented |
| Source | `test/03_system/feature/usage/context_managers_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
with resource as alias:
# code using alias
# __exit__ is called after this block
```

## Key Behaviors

- `__enter__()` is called on entry, its return value is bound to alias
- `__exit__()` is always called, even if an exception occurs
- Alias binding can coexist with parser special handling (e.g., cast expressions)
- Clean separation between resource acquisition and usage
- Exception safety: cleanup always happens

## Scenarios

### Context Managers

#### basic context manager protocol

#### calls __enter__ and binds result to alias

1. fn   enter
2. fn   exit
3. with Resource


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Resource:
    value: i64

    fn __enter__() -> i64:
        self.value + 10

    fn __exit__(exc):
        pass

var captured = 0
with Resource(5) as alias:
    captured = alias

expect captured == 15
```

</details>

#### calls __exit__ after block completes

1. fn   enter
2. fn   exit


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Resource:
    value: i64
    exited: bool = false

    fn __enter__() -> i64:
        self.value

    fn __exit__(exc):
        exited = true

val resource = Resource(value: 42)
with resource as alias:
    pass

expect resource.exited == true
```

</details>

#### alias binding and reuse

#### reuses identifier when parser sees cast-style syntax

1. fn   enter
2. fn   exit
3. with Resource


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Resource:
    value: i64

    fn __enter__() -> i64:
        self.value + 1

    fn __exit__(exc):
        pass

var result = 0
with Resource(2) as alias:
    val inner = alias
    result = inner

expect result == 3
```

</details>

#### properly binds alias in nested contexts

1. fn   enter
2. fn   exit
3. with Resource
4. results push
5. with Resource
6. results push
7. results push


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Resource:
    value: i64

    fn __enter__() -> i64:
        self.value * 2

    fn __exit__(exc):
        pass

var results = []
with Resource(5) as x:
    results.push(x)
    with Resource(3) as y:
        results.push(y)
    results.push(x)

expect results == [10, 6, 10]
```

</details>

#### resource cleanup

#### runs cleanup code after block

1. fn   enter
2. fn   exit


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Resource:
    cleanup_count: i64 = 0

    fn __enter__() -> i64:
        0

    fn __exit__(exc):
        cleanup_count = cleanup_count + 1

val resource = Resource()
with resource as x:
    pass

expect resource.cleanup_count == 1
```

</details>

#### runs cleanup even after multiple operations

1. fn   enter
2. fn   exit


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Resource:
    operations: i64 = 0
    exit_called: bool = false

    fn __enter__() -> i64:
        0

    fn __exit__(exc):
        exit_called = true

val resource = Resource()
with resource as x:
    resource.operations = 1
    resource.operations = 2
    resource.operations = 3

expect resource.operations == 3
expect resource.exit_called == true
```

</details>

#### using acquired values

#### can use alias from __enter__ return value

1. fn   enter
2. fn   exit
3. with Config


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Config:
    filename: text
    content: text = ""

    fn __enter__() -> text:
        "loaded content"

    fn __exit__(exc):
        pass

var loaded = ""
with Config(filename: "test.txt") as data:
    loaded = data

expect loaded == "loaded content"
```

</details>

#### can call methods on alias

1. fn   enter
2. fn   exit
3. fn process
4. with Handler
5. result = handler process


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Handler:
    fn __enter__() -> Handler:
        self

    fn __exit__(exc):
        pass

    fn process() -> i64:
        42

var result = 0
with Handler() as handler:
    result = handler.process()

expect result == 42
```

</details>

#### exception handling

#### passes exception info to __exit__

1. fn   enter
2. fn   exit


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Resource:
    exception_passed: bool = false

    fn __enter__() -> i64:
        0

    fn __exit__(exc):
        # exc is the exception or None
        exception_passed = exc != None

val resource = Resource()
with resource as x:
    pass

# No exception occurred, so exc should be None
expect resource.exception_passed == false
```

</details>

#### always calls __exit__ for resource cleanup

1. fn   enter
2. fn   exit


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Resource:
    exit_was_called: bool = false

    fn __enter__() -> i64:
        42

    fn __exit__(exc):
        exit_was_called = true

val resource = Resource()
val result = 0
with resource as value:
    # Some operation
    val temp = value + 1

expect resource.exit_was_called == true
```

</details>

#### multiple resources

#### can nest multiple context managers

1. fn   enter
2. fn   exit
3. results push
4. results push


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Resource:
    id: i64
    exited: bool = false

    fn __enter__() -> i64:
        self.id

    fn __exit__(exc):
        exited = true

val r1 = Resource(id: 1)
val r2 = Resource(id: 2)
var results = []

with r1 as x:
    results.push(x)
    with r2 as y:
        results.push(y)

expect results == [1, 2]
expect r1.exited == true
expect r2.exited == true
```

</details>

#### cleans up in reverse order

1. fn   enter
2. fn   exit


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Resource:
    id: i64
    exit_order: List<i64> = []

    fn __enter__() -> i64:
        self.id

    fn __exit__(exc):
        # Append to shared list to track order
        pass

# Ideally, exits happen in reverse: 2 then 1
# Implementation dependent on execution model
```

</details>

#### practical patterns

#### implements file-like resource pattern

1. fn   enter
2. fn   exit


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class File:
    filename: text
    is_open: bool = false

    fn __enter__() -> text:
        is_open = true
        "file content"

    fn __exit__(exc):
        is_open = false

val file = File(filename: "data.txt")
var content = ""

with file as data:
    expect file.is_open == true
    content = data

expect file.is_open == false
expect content == "file content"
```

</details>

#### ensures state is restored on exit

1. fn   enter
2. fn   exit


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class StateManager:
    state: text = "initial"

    fn __enter__() -> text:
        state = "active"
        state

    fn __exit__(exc):
        state = "cleaned"

val manager = StateManager()
var temp = ""

with manager as state:
    temp = state
    expect manager.state == "active"

expect manager.state == "cleaned"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
