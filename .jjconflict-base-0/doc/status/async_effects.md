# Feature #32: Async Effects

**Status**: Implemented
**Difficulty**: 4 (was 5)
**Importance**: 3

## Summary

Async effects ensure functions don't block, enabling safe use in latency-critical contexts.

## Implemented Syntax

```simple
async fn fast_operation(x: i64) -> i64:
    # Cannot call blocking operations
    return x * 2

async fn blocking_operation():
    # Can call blocking operations
    let result = await some_future
    return result

fn normal_operation():
    # Can call async functions
    let result = fast_operation(21)
    # Can also do blocking operations
    let data = read_file("data.txt")
```

## Features Implemented

- [x] `async` function annotation
- [x] Effect checking at runtime
- [x] Prevent blocking calls in async functions
- [x] Blocking operations list: recv, join, await, sleep, read_file, write_file, print, println, input
- [ ] Prevent GC allocation in async functions (future enhancement)
- [ ] Effect inference (future enhancement)
- [ ] Effect polymorphism (future enhancement)

## Implementation Details

### Parser Changes
- Added `parse_async_function()` and `parse_async_function()` methods
- Updated `parse_item()` and `parse_pub_item()` to handle `TokenKind::Async` and `TokenKind::Async`
- Functions can be annotated with `async fn` or `async fn`

### Runtime Effect Checking
- Added `CURRENT_EFFECT` thread-local to track current effect context
- Added `BLOCKING_OPERATIONS` list of operations that cannot be called from async context
- Added `check_async_violation()` function that errors if blocking op called in async fn
- Modified `exec_function()` to save/restore effect context during function calls

### Blocking Operations
The following operations are blocked in async functions:
- `recv` - Blocking receive from channel
- `join` - Wait for actor/thread to complete
- `await` - Wait for future to complete
- `sleep` - Thread sleep
- `read_file` - File I/O
- `write_file` - File I/O
- `print` - Console output
- `println` - Console output
- `input` - Console input

### Error Messages
When a blocking operation is used in a async function:
```
semantic: blocking operation 'print' not allowed in async function
```

## Tests

- `interpreter_async_basic` - Async fn can do non-blocking computation
- `interpreter_async_blocks_print` - Async fn cannot use print
- `interpreter_async_blocks_await` - Async fn cannot use await
- `interpreter_async_fn_basic` - Async fn can use blocking operations
- `interpreter_async_can_call_async` - Async fn can call other async fns

## Related

- #30 Actors (Implemented)
- #31 Concurrency Primitives (Implemented)
- #33 Stackless Coroutines (Pending)
