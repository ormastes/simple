# Async File I/O Specification
*Source:* `test/feature/usage/async_file_io_spec.spl`
**Feature IDs:** #ASYNC-FILE-001 to #ASYNC-FILE-007  |  **Category:** Runtime | File I/O  |  **Status:** Implemented

## Overview



Tests async file I/O functionality including:
- Async file handle creation
- File loading lifecycle (Pending -> Loading -> Ready/Failed)
- Invalid path handling
- Invalid handle errors
- Multiple concurrent file handles
- Prefault option for memory-mapped files
- Input validation

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

## Feature: Async File Creation

## File Handle Creation

    Tests async file handle creation and initial state.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates handle for existing file | pass |
| 2 | initial state is Pending | pass |
| 3 | is not ready before loading | pass |

**Example:** creates handle for existing file
    Given val path = "/tmp/test_async_create.txt"
    Then  expect test_create_handle() > 0

**Example:** initial state is Pending
    Then  expect get_initial_state() == 0

**Example:** is not ready before loading
    Then  expect not check_not_ready_initially()

## Feature: File Loading Lifecycle

## Loading State Transitions

    Tests the complete async file loading lifecycle.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | transitions through states correctly | pass |
| 2 | wait returns valid data pointer | pass |
| 3 | is ready after successful load | pass |

**Example:** transitions through states correctly
    Then  expect test_lifecycle() == 1

**Example:** wait returns valid data pointer
    Then  expect test_wait_returns_data()

**Example:** is ready after successful load
    Then  expect test_is_ready_after_load()

## Feature: Async File Error Handling

## Error Cases

    Tests error handling for invalid paths and handles.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | handles invalid path gracefully | pass |
| 2 | wait returns zero for failed load | pass |
| 3 | invalid handle returns failed state | pass |
| 4 | invalid handle wait returns zero | pass |

**Example:** handles invalid path gracefully
    Then  expect test_invalid_path() == 2

**Example:** wait returns zero for failed load
    Then  expect test_failed_wait() == 0

**Example:** invalid handle returns failed state
    Then  expect test_invalid_handle() == 2

**Example:** invalid handle wait returns zero
    Then  expect test_invalid_handle_wait() == 0

## Feature: Multiple Async File Handles

## Concurrent File Loading

    Tests handling multiple async file operations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | creates unique handle IDs | pass |
| 2 | loads multiple files concurrently | pass |

**Example:** creates unique handle IDs
    Given val handle1 = 1
    Given val handle2 = 2
    Then  expect test_unique_handles()

**Example:** loads multiple files concurrently
    Then  expect test_concurrent_load()

## Feature: Async File Advanced Options

## Memory-Mapped File Options

    Tests advanced options like prefaulting.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | supports prefault option | pass |
| 2 | rejects non-string path input | pass |

**Example:** supports prefault option
    Then  expect test_prefault()

**Example:** rejects non-string path input
    Then  expect test_invalid_input() == 0


