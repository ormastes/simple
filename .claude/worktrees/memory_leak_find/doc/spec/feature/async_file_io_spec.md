# Async File I/O Specification

**Feature ID:** #ASYNC-FILE-001 to #ASYNC-FILE-007 | **Category:** Runtime | File I/O | **Status:** Implemented

_Source: `test/feature/usage/async_file_io_spec.spl`_

---

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

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 14 |

## Test Structure

### Async File Creation

- ✅ creates handle for existing file
- ✅ initial state is Pending
- ✅ is not ready before loading
### File Loading Lifecycle

- ✅ transitions through states correctly
- ✅ wait returns valid data pointer
- ✅ is ready after successful load
### Async File Error Handling

- ✅ handles invalid path gracefully
- ✅ wait returns zero for failed load
- ✅ invalid handle returns failed state
- ✅ invalid handle wait returns zero
### Multiple Async File Handles

- ✅ creates unique handle IDs
- ✅ loads multiple files concurrently
### Async File Advanced Options

- ✅ supports prefault option
- ✅ rejects non-string path input

