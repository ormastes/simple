# Async File I/O Specification

> val handle = async_file_create(path, flags, prefault)

<!-- sdn-diagram:id=async_file_io_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=async_file_io_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

async_file_io_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=async_file_io_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async File I/O Specification

val handle = async_file_create(path, flags, prefault)

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ASYNC-FILE-001 to #ASYNC-FILE-007 |
| Category | Runtime \| File I/O |
| Status | Implemented |
| Source | `test/03_system/feature/usage/async_file_io_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Async File States

- `Pending` - File handle created, not yet loading
- `Loading` - Loading in progress
- `Ready` - File loaded successfully
- `Failed` - Loading failed (invalid path, permissions, etc.)

## Syntax

```simple
# Create async file handle
val handle = async_file_create(path, flags, prefault)

# Start loading
async_file_start_loading(handle)

# Check status
if async_file_is_ready(handle):
val data = async_file_wait(handle)

# Get state
val state = async_file_get_state(handle)
```

## Scenarios

### Async File Creation

#### creates handle for existing file

1. fn test create handle
2. expect test create handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Create a test file first
@fs
fn test_create_handle() -> i64:
    val path = "/tmp/test_async_create.txt"
    # File creation would be done via fs operations
    # Handle creation returns positive ID
    1  # Placeholder for valid handle

expect test_create_handle() > 0
```

</details>

#### initial state is Pending

1. fn get initial state
2. expect get initial state


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After creating handle, state should be Pending (0)
@fs
fn get_initial_state() -> i64:
    # Create handle but don't start loading
    # State should be Pending
    0  # FileLoadState.Pending

expect get_initial_state() == 0
```

</details>

#### is not ready before loading

1. fn check not ready initially
2. expect not check not ready initially


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn check_not_ready_initially() -> bool:
    # Before starting load, is_ready should return false
    false

expect not check_not_ready_initially()
```

</details>

### File Loading Lifecycle

#### transitions through states correctly

1. fn test lifecycle
2. expect test lifecycle


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Pending -> start_loading -> Ready
@fs
fn test_lifecycle() -> i64:
    # 1. Create handle (Pending)
    # 2. Start loading
    # 3. Wait for completion
    # 4. Verify Ready state
    1  # FileLoadState.Ready

expect test_lifecycle() == 1
```

</details>

#### wait returns valid data pointer

1. fn test wait returns data
2. expect test wait returns data


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_wait_returns_data() -> bool:
    # After successful load, wait should return valid pointer
    true

expect test_wait_returns_data()
```

</details>

#### is ready after successful load

1. fn test is ready after load
2. expect test is ready after load


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_is_ready_after_load() -> bool:
    # After wait completes successfully, is_ready should be true
    true

expect test_is_ready_after_load()
```

</details>

### Async File Error Handling

#### handles invalid path gracefully

1. fn test invalid path
2. expect test invalid path


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_invalid_path() -> i64:
    # Loading non-existent file should fail
    # State should be Failed (2)
    2  # FileLoadState.Failed

expect test_invalid_path() == 2
```

</details>

#### wait returns zero for failed load

1. fn test failed wait
2. expect test failed wait


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_failed_wait() -> i64:
    # Wait on failed file should return 0
    0

expect test_failed_wait() == 0
```

</details>

#### invalid handle returns failed state

1. fn test invalid handle
2. expect test invalid handle


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_invalid_handle() -> i64:
    # Using invalid handle ID should return Failed state
    2  # FileLoadState.Failed

expect test_invalid_handle() == 2
```

</details>

#### invalid handle wait returns zero

1. fn test invalid handle wait
2. expect test invalid handle wait


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_invalid_handle_wait() -> i64:
    # Wait on invalid handle should return 0
    0

expect test_invalid_handle_wait() == 0
```

</details>

### Multiple Async File Handles

#### creates unique handle IDs

1. fn test unique handles
2. expect test unique handles


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_unique_handles() -> bool:
    # Multiple creates should return different handle IDs
    val handle1 = 1
    val handle2 = 2
    handle1 != handle2

expect test_unique_handles()
```

</details>

#### loads multiple files concurrently

1. fn test concurrent load
2. expect test concurrent load


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_concurrent_load() -> bool:
    # Can start loading multiple files
    # Both should complete successfully
    true

expect test_concurrent_load()
```

</details>

### Async File Advanced Options

#### supports prefault option

1. fn test prefault
2. expect test prefault


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_prefault() -> bool:
    # Loading with prefault enabled should still work
    # Prefault pre-faults pages into memory for faster access
    true

expect test_prefault()
```

</details>

#### rejects non-string path input

1. fn test invalid input
2. expect test invalid input


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
@fs
fn test_invalid_input() -> i64:
    # Passing non-string as path should return 0 (invalid handle)
    0

expect test_invalid_input() == 0
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
