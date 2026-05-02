# Async File I/O Specification

Tests async file I/O functionality including:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #ASYNC-FILE-001 to #ASYNC-FILE-007 |
| Category | Runtime \| File I/O |
| Status | Implemented |
| Source | `test/feature/usage/async_file_io_spec.spl` |
| Updated | 2026-04-07 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

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
val handle = async_file_create(path, flags, prefault)

async_file_start_loading(handle)

if async_file_is_ready(handle):
val data = async_file_wait(handle)

val state = async_file_get_state(handle)
```

## Evidence

| Category | Count |
|----------|------:|
| Artifacts | 1 |

### Artifacts

| Item | Kind | Path |
|------|------|------|
| `result.json` | JSON artifact | `build/test-artifacts/feature/usage/async_file_io/result.json` |

## Scenarios

- creates handle for existing file
- initial state is Pending
- is not ready before loading
- transitions through states correctly
- wait returns valid data pointer
- is ready after successful load
- handles invalid path gracefully
- wait returns zero for failed load
- invalid handle returns failed state
- invalid handle wait returns zero
- creates unique handle IDs
- loads multiple files concurrently
- supports prefault option
- rejects non-string path input
