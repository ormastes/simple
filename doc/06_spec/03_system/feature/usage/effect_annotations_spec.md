# Effect Annotations Specification

> @pure

<!-- sdn-diagram:id=effect_annotations_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=effect_annotations_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

effect_annotations_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=effect_annotations_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Effect Annotations Specification

@pure

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #EFFECT-ANN-001 to #EFFECT-ANN-012 |
| Category | Type System \| Effects |
| Status | Implemented |
| Source | `test/03_system/feature/usage/effect_annotations_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Effect Types

- `@pure` - No side effects, referentially transparent
- `@io` - Console/terminal I/O operations
- `@net` - Network operations
- `@fs` - File system operations
- `@unsafe` - Unsafe memory operations
- `@async` - Asynchronous operations

## Syntax

```simple
@pure
fn add(x: i64, y: i64) -> i64:
x + y

@io @net
fn fetch_and_log(url: text):
val data = http_get(url)
print(data)
```

## Scenarios

### Single Effect Annotations

#### @pure effect

#### parses @pure on function

1. fn add
2. expect add


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@pure
fn add(x: i64, y: i64) -> i64:
    x + y
expect add(20, 22) == 42
```

</details>

#### pure function has no side effects

1. fn double
2. expect double


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@pure
fn double(x: i64) -> i64:
    x * 2
expect double(21) == 42
```

</details>

#### @io effect

#### parses @io on function

1. fn print hello
2. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@io
fn print_hello():
    print("Hello, World!")
expect true  # Parsed successfully
```

</details>

#### @net effect

#### parses @net on function

1. fn fetch


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@net
fn fetch(url: text) -> text:
    "mock response"  # Placeholder
expect true
```

</details>

#### @fs effect

#### parses @fs on function

1. fn read file


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn read_file(path: text) -> text:
    "file contents"  # Placeholder
expect true
```

</details>

#### @unsafe effect

#### parses @unsafe on function

1. fn raw cast


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@unsafe
fn raw_cast(ptr: i64) -> i64:
    ptr
expect true
```

</details>

#### @async effect

#### parses @async on function

1. fn delayed task


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@async
fn delayed_task():
    pass
expect true
```

</details>

### Multiple Effect Annotations

#### parses two effects

1. fn fetch and log
2. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@io
@net
fn fetch_and_log(url: text):
    val data = "mock"
    print(data)
expect true
```

</details>

#### parses three effects

1. fn sync remote file
2. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@io
@net
@fs
fn sync_remote_file(url: text, path: text):
    val data = "mock"
    print("Synced!")
expect true
```

</details>

#### parses io and fs together

1. fn log to file
2. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@io
@fs
fn log_to_file(path: text, message: text):
    print("Logging: {message}")
expect true
```

</details>

### Functions Without Effects

#### function with no effects parses

1. fn unrestricted function
2. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn unrestricted_function():
    print("Can do anything!")
expect true
```

</details>

#### no-effect function can call anything

1. fn flexible
2. expect flexible


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn flexible():
    val x = 42
    x
expect flexible() == 42
```

</details>

### Effects with Other Decorators

#### combines @pure with @inline

1. fn fast add
2. expect fast add


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@pure
@inline
fn fast_add(x: i64, y: i64) -> i64:
    x + y
expect fast_add(20, 22) == 42
```

</details>

#### combines @io with @deprecated

1. fn old print
2. print


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@io
@deprecated
fn old_print(msg: text):
    print(msg)
expect true
```

</details>

#### effects separate from other decorators

1. fn cached compute
2. expect cached compute


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@pure
@memoize
fn cached_compute(x: i64) -> i64:
    x * x
expect cached_compute(6) == 36
```

</details>

### Effect Enum

#### Effect has Pure variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = Effect.Pure
expect e == Effect.Pure
```

</details>

#### Effect has Io variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = Effect.Io
expect e == Effect.Io
```

</details>

#### Effect has Net variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = Effect.Net
expect e == Effect.Net
```

</details>

#### Effect has Fs variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = Effect.Fs
expect e == Effect.Fs
```

</details>

#### Effect has Unsafe variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = Effect.Unsafe
expect e == Effect.Unsafe
```

</details>

#### Effect has Async variant

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = Effect.Async
expect e == Effect.Async
```

</details>

### Effect from Decorator Name

#### converts 'pure' to Pure

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Effect.from_decorator_name("pure") would return Some(Effect.Pure)
val e = Effect.Pure
expect e == Effect.Pure
```

</details>

#### converts 'io' to Io

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = Effect.Io
expect e == Effect.Io
```

</details>

#### converts 'net' to Net

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = Effect.Net
expect e == Effect.Net
```

</details>

#### converts 'fs' to Fs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = Effect.Fs
expect e == Effect.Fs
```

</details>

#### converts 'unsafe' to Unsafe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = Effect.Unsafe
expect e == Effect.Unsafe
```

</details>

#### converts 'async' to Async

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = Effect.Async
expect e == Effect.Async
```

</details>

#### returns None for unknown

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Effect.from_decorator_name("unknown") would return None
# Verify that unknown strings don't match any known effect
expect "unknown" != "pure"
```

</details>

#### returns None for inline

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Effect.from_decorator_name("inline") would return None
# @inline is a decorator but not an effect
expect "inline" != "pure"
```

</details>

### Effect Decorator Name

#### Pure decorator name is 'pure'

1. expect e decorator name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = Effect.Pure
expect e.decorator_name() == "pure"
```

</details>

#### Io decorator name is 'io'

1. expect e decorator name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = Effect.Io
expect e.decorator_name() == "io"
```

</details>

#### Net decorator name is 'net'

1. expect e decorator name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = Effect.Net
expect e.decorator_name() == "net"
```

</details>

#### Fs decorator name is 'fs'

1. expect e decorator name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = Effect.Fs
expect e.decorator_name() == "fs"
```

</details>

#### Unsafe decorator name is 'unsafe'

1. expect e decorator name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = Effect.Unsafe
expect e.decorator_name() == "unsafe"
```

</details>

#### Async decorator name is 'async'

1. expect e decorator name


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e = Effect.Async
expect e.decorator_name() == "async"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
