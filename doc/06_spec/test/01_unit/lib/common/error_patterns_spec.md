# Error Patterns Specification

> <details>

<!-- sdn-diagram:id=error_patterns_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=error_patterns_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

error_patterns_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=error_patterns_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Patterns Specification

## Scenarios

### ErrorKind constants

#### has NotFound kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ERROR_NOT_FOUND).to_equal("not found")
```

</details>

#### has PermissionDenied kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ERROR_PERMISSION_DENIED).to_equal("permission denied")
```

</details>

#### has InvalidInput kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ERROR_INVALID_INPUT).to_equal("invalid input")
```

</details>

#### has InvalidData kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ERROR_INVALID_DATA).to_equal("invalid data")
```

</details>

#### has Unknown kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ERROR_UNKNOWN).to_equal("unknown error")
```

</details>

#### has TimedOut kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ERROR_TIMED_OUT).to_equal("timed out")
```

</details>

#### has AlreadyExists kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ERROR_ALREADY_EXISTS).to_equal("already exists")
```

</details>

#### has all 13 error kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kinds = [ERROR_NOT_FOUND, ERROR_PERMISSION_DENIED, ERROR_CONNECTION_REFUSED, ERROR_CONNECTION_RESET, ERROR_INTERRUPTED, ERROR_TIMED_OUT, ERROR_INVALID_INPUT, ERROR_INVALID_DATA, ERROR_UNEXPECTED_EOF, ERROR_ALREADY_EXISTS, ERROR_WOULD_BLOCK, ERROR_OTHER, ERROR_UNKNOWN]
expect(kinds.len()).to_equal(13)
```

</details>

### simple_error

#### creates error with kind and message

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = simple_error(ERROR_NOT_FOUND, "File not found: data.txt")
expect(error_message(err)).to_equal("File not found: data.txt")
expect(error_kind(err)).to_equal("not found")
```

</details>

#### creates error with nil source

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = simple_error(ERROR_UNKNOWN, "something failed")
val src = error_source(err)
expect(src).to_be_nil()
```

</details>

### simple_error_with_source

#### creates error with source chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = simple_error(ERROR_NOT_FOUND, "file missing")
val outer = simple_error_with_source(ERROR_INVALID_DATA, "config load failed", inner)
expect(error_message(outer)).to_equal("config load failed")
expect(error_kind(outer)).to_equal("invalid data")
val src = error_source(outer)
expect(error_message(src)).to_equal("file missing")
expect(error_kind(src)).to_equal("not found")
```

</details>

#### creates deep error chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e1 = simple_error(ERROR_CONNECTION_REFUSED, "server down")
val e2 = simple_error_with_source(ERROR_TIMED_OUT, "request failed", e1)
val e3 = simple_error_with_source(ERROR_OTHER, "operation failed", e2)
expect(error_message(e3)).to_equal("operation failed")
val src2 = error_source(e3)
expect(error_message(src2)).to_equal("request failed")
val src1 = error_source(src2)
expect(error_message(src1)).to_equal("server down")
val src0 = error_source(src1)
expect(src0).to_be_nil()
```

</details>

### make_error

#### creates error with Unknown kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = make_error("something went wrong")
expect(error_message(err)).to_equal("something went wrong")
expect(error_kind(err)).to_equal("unknown error")
```

</details>

### make_io_error

#### creates IO error with specified kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = make_io_error(ERROR_NOT_FOUND, "file.txt not found")
expect(error_message(err)).to_equal("file.txt not found")
expect(error_kind(err)).to_equal("not found")
```

</details>

#### creates different IO error kinds

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e1 = make_io_error(ERROR_PERMISSION_DENIED, "access denied")
val e2 = make_io_error(ERROR_TIMED_OUT, "connection timed out")
expect(error_kind(e1)).to_equal("permission denied")
expect(error_kind(e2)).to_equal("timed out")
```

</details>

### make_validation_error

#### creates validation error with InvalidInput kind

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = make_validation_error("email format invalid")
expect(error_message(err)).to_equal("email format invalid")
expect(error_kind(err)).to_equal("invalid input")
```

</details>

### format_error

#### formats single error

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = simple_error(ERROR_NOT_FOUND, "file missing")
val formatted = format_error(err)
expect(formatted).to_equal("Error: file missing")
```

</details>

#### formats error with source chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = simple_error(ERROR_NOT_FOUND, "file missing")
val outer = simple_error_with_source(ERROR_INVALID_DATA, "config load failed", inner)
val formatted = format_error(outer)
expect(formatted).to_contain("Error: config load failed")
expect(formatted).to_contain("Caused by: file missing")
```

</details>

#### formats deep error chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e1 = simple_error(ERROR_CONNECTION_REFUSED, "server down")
val e2 = simple_error_with_source(ERROR_TIMED_OUT, "request failed", e1)
val e3 = simple_error_with_source(ERROR_OTHER, "operation failed", e2)
val formatted = format_error(e3)
expect(formatted).to_contain("Error: operation failed")
expect(formatted).to_contain("Caused by: request failed")
expect(formatted).to_contain("Caused by: server down")
```

</details>

### format_error_compact

#### formats single error compactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = simple_error(ERROR_NOT_FOUND, "file missing")
val formatted = format_error_compact(err)
expect(formatted).to_equal("file missing")
```

</details>

#### formats error chain with colons

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val inner = simple_error(ERROR_NOT_FOUND, "file missing")
val outer = simple_error_with_source(ERROR_INVALID_DATA, "config load failed", inner)
val formatted = format_error_compact(outer)
expect(formatted).to_equal("config load failed: file missing")
```

</details>

#### formats deep chain compactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val e1 = simple_error(ERROR_CONNECTION_REFUSED, "server down")
val e2 = simple_error_with_source(ERROR_TIMED_OUT, "request failed", e1)
val e3 = simple_error_with_source(ERROR_OTHER, "operation failed", e2)
val formatted = format_error_compact(e3)
expect(formatted).to_equal("operation failed: request failed: server down")
```

</details>

### error handling patterns

#### uses nil for no error (option pattern)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var current_error = nil
# Simulate successful operation
val result = 42
expect(current_error).to_be_nil()
expect(result).to_equal(42)
```

</details>

#### uses error dict for failure (option pattern)

1. current error = make error
   - Expected: has_error is true
   - Expected: error_message(current_error) equals `operation failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var current_error = nil
# Simulate failed operation
current_error = make_error("operation failed")
val has_error = current_error != nil
expect(has_error).to_equal(true)
expect(error_message(current_error)).to_equal("operation failed")
```

</details>

#### propagates errors through chain

1. fn inner op
2. make io error
3. fn outer op
4. simple error with source
   - Expected: error_kind(final_err) equals `invalid data`
   - Expected: error_kind(src) equals `not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn inner_op() -> dict:
    make_io_error(ERROR_NOT_FOUND, "data.txt not found")
fn outer_op() -> dict:
    val err = inner_op()
    simple_error_with_source(ERROR_INVALID_DATA, "cannot load config", err)
val final_err = outer_op()
expect(error_kind(final_err)).to_equal("invalid data")
val src = error_source(final_err)
expect(error_kind(src)).to_equal("not found")
```

</details>

#### handles multiple error kinds differently

1. fn handle error
   - Expected: handle_error(e1) equals `retry with default`
   - Expected: handle_error(e2) equals `request access`
   - Expected: handle_error(e3) equals `retry later`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn handle_error(err: dict) -> text:
    val kind = error_kind(err)
    if kind == ERROR_NOT_FOUND:
        return "retry with default"
    if kind == ERROR_PERMISSION_DENIED:
        return "request access"
    if kind == ERROR_TIMED_OUT:
        return "retry later"
    "unknown handling"
val e1 = make_io_error(ERROR_NOT_FOUND, "missing")
val e2 = make_io_error(ERROR_PERMISSION_DENIED, "denied")
val e3 = make_io_error(ERROR_TIMED_OUT, "slow")
expect(handle_error(e1)).to_equal("retry with default")
expect(handle_error(e2)).to_equal("request access")
expect(handle_error(e3)).to_equal("retry later")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/error_patterns_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ErrorKind constants
- simple_error
- simple_error_with_source
- make_error
- make_io_error
- make_validation_error
- format_error
- format_error_compact
- error handling patterns

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
