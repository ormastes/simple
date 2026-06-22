# Effect System Specification

> requires [pure, io]

<!-- sdn-diagram:id=effect_system_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=effect_system_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

effect_system_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=effect_system_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Effect System Specification

requires [pure, io]

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #EFFECT-SYS-001 to #EFFECT-SYS-040 |
| Category | Type System \| Effects |
| Status | Implemented |
| Source | `test/03_system/feature/usage/effect_system_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Effect Types

- `@pure` - No side effects, referentially transparent
- `@io` - Console/terminal I/O operations
- `@net` - Network operations
- `@fs` - File system operations
- `@unsafe` - Unsafe memory operations
- `@async` - Asynchronous operations

## Capabilities

- `requires [cap1, cap2]` - Module capability requirements
- Effect validation at compile time

## Syntax

```simple
requires [pure, io]

@pure
fn add(x: i64, y: i64) -> i64:
x + y

@io @net
fn fetch_and_log(url: text) -> text:
val data = http_get(url)
print(data)
data
```

## Scenarios

### @pure Effect

#### pure function can do computation

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@pure
fn add(x: i64, y: i64) -> i64:
    x + y

expect add(20, 22) == 42
```

</details>

#### pure function can call other pure functions

1. fn double
2. fn quadruple
3. double
4. expect quadruple


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@pure
fn double(x: i64) -> i64:
    x * 2

@pure
fn quadruple(x: i64) -> i64:
    double(double(x))

expect quadruple(10) == 40
```

</details>

#### pure function blocks print

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This would be a compile error:
# @pure
# fn bad():
#     print("hello")  # Error: I/O not allowed in pure function
expect true  # Compile-time check
```

</details>

### @io Effect

#### io function can do computation

1. fn compute and return
2. expect compute and return


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@io
fn compute_and_return(x: i64) -> i64:
    x * 2

expect compute_and_return(21) == 42
```

</details>

### @async Effect

#### async decorator syntax works

1. fn compute
2. expect compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@async
fn compute(x: i64) -> i64:
    x * 2

expect compute(21) == 42
```

</details>

#### async allows non-blocking io

1. fn greet
2. print
3. expect greet


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@async
fn greet() -> i64:
    print("hello")
    42

expect greet() == 42
```

</details>

### @fs Effect

#### fs function can do computation

1. fn compute fs
2. expect compute fs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn compute_fs(x: i64) -> i64:
    x * 2

expect compute_fs(21) == 42
```

</details>

### @net Effect

#### net function can do computation

1. fn compute net
2. expect compute net


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@net
fn compute_net(x: i64) -> i64:
    x * 2

expect compute_net(21) == 42
```

</details>

### @unsafe Effect

#### unsafe function can do computation

1. fn compute unsafe
2. expect compute unsafe


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@unsafe
fn compute_unsafe(x: i64) -> i64:
    x * 2

expect compute_unsafe(21) == 42
```

</details>

### Stacked Effects

#### pure and async together

1. fn fast compute
2. expect fast compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@pure
@async
fn fast_compute(x: i64) -> i64:
    x * 2

expect fast_compute(21) == 42
```

</details>

#### io and net together

1. fn network logger
2. expect network logger


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@io
@net
fn network_logger(x: i64) -> i64:
    x * 2

expect network_logger(21) == 42
```

</details>

#### all effects together

1. fn full access
2. expect full access


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@io
@net
@fs
fn full_access(x: i64) -> i64:
    x * 2

expect full_access(21) == 42
```

</details>

#### all effects parsed

1. fn all effects
2. expect all effects


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@pure
@io
@net
@fs
@unsafe
fn all_effects(x: i64) -> i64:
    x

expect all_effects(42) == 42
```

</details>

### Effect with Attributes

#### effects with inline attribute

1. fn attributed pure
2. expect attributed pure


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@inline
@pure
fn attributed_pure(x: i64) -> i64:
    x * 2

expect attributed_pure(21) == 42
```

</details>

### Unrestricted Functions

#### unrestricted function works

1. fn do anything
2. expect do anything


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn do_anything(x: i64) -> i64:
    x * 2

expect do_anything(21) == 42
```

</details>

### Effect Propagation

#### pure cannot call io

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This would be a compile error:
# @io fn log_value(x: i64) -> i64: ...
# @pure fn compute(x: i64) -> i64: log_value(x) * 2  # Error
expect true  # Compile-time check
```

</details>

#### pure cannot call net

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This would be a compile error:
# @net fn fetch_data() -> i64: ...
# @pure fn process() -> i64: fetch_data() * 2  # Error
expect true  # Compile-time check
```

</details>

#### pure cannot call fs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This would be a compile error:
# @fs fn read_config() -> i64: ...
# @pure fn get_value() -> i64: read_config() + 10  # Error
expect true  # Compile-time check
```

</details>

#### pure cannot call unsafe

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This would be a compile error:
# @unsafe fn dangerous() -> i64: ...
# @pure fn safe_wrapper() -> i64: dangerous() + 1  # Error
expect true  # Compile-time check
```

</details>

#### io can call pure

1. fn calculate
2. fn log and compute
3. calculate
4. expect log and compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@pure
fn calculate(x: i64) -> i64:
    x * 2

@io
fn log_and_compute(x: i64) -> i64:
    calculate(x) + 10

expect log_and_compute(20) == 50
```

</details>

#### io can call io

1. fn helper
2. fn caller
3. helper
4. expect caller


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@io
fn helper(x: i64) -> i64:
    x * 2

@io
fn caller(x: i64) -> i64:
    helper(x) + 10

expect caller(20) == 50
```

</details>

#### unrestricted can call anything

1. fn io func
2. fn net func
3. fn fs func
4. fn pure func
5. fn unrestricted
6. io func
7. expect unrestricted


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@io
fn io_func() -> i64:
    10

@net
fn net_func() -> i64:
    20

@fs
fn fs_func() -> i64:
    30

@pure
fn pure_func() -> i64:
    5

fn unrestricted() -> i64:
    io_func() + net_func() + fs_func() + pure_func()

expect unrestricted() == 65
```

</details>

### Capability Requirements

#### basic capability parsing

1. fn compute
2. expect compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
requires [pure]

@pure
fn compute(x: i64) -> i64:
    x * 2

expect compute(21) == 42
```

</details>

#### multiple capabilities

1. fn compute
2. expect compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
requires [pure, io, net]

@pure
fn compute(x: i64) -> i64:
    x * 2

expect compute(21) == 42
```

</details>

#### all capabilities

1. fn compute
2. expect compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
requires [pure, io, net, fs, unsafe, gc]

fn compute(x: i64) -> i64:
    x * 2

expect compute(21) == 42
```

</details>

#### trailing comma allowed

1. fn compute
2. expect compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
requires [pure, io,]

@pure
fn compute(x: i64) -> i64:
    x * 2

expect compute(21) == 42
```

</details>

#### empty requires list

1. fn compute
2. expect compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
requires []

fn compute(x: i64) -> i64:
    x * 2

expect compute(21) == 42
```

</details>

### Compile-Time Capability Validation

#### effect matches capability

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
requires [pure]

@pure
fn add(x: i64, y: i64) -> i64:
    x + y

expect add(20, 22) == 42
```

</details>

#### io effect blocked by pure-only module

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This would be a compile error:
# requires [pure]
# @io fn log_value(x: i64) -> i64: x  # Error: @io not in [pure]
expect true  # Compile-time check
```

</details>

#### async always allowed

1. fn compute
2. expect compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
requires [pure]

@async
fn compute(x: i64) -> i64:
    x * 2

expect compute(21) == 42
```

</details>

#### multiple effects with matching capabilities

1. fn process
2. expect process


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
requires [pure, io]

@pure
@io
fn process(x: i64) -> i64:
    x * 2

expect process(21) == 42
```

</details>

#### unrestricted module allows all

1. fn do everything
2. expect do everything


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@io
@net
@fs
@unsafe
fn do_everything(x: i64) -> i64:
    x * 2

expect do_everything(21) == 42
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
