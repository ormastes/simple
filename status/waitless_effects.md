# Feature #32: Waitless Effects

**Status**: Implemented
**Difficulty**: 4 (was 5)
**Importance**: 3

## Summary

Waitless effects ensure functions don't block, enabling safe use in latency-critical contexts.

## Implemented Syntax

```simple
waitless fn fast_operation(x: i64) -> i64:
    # Cannot call blocking operations
    return x * 2

async fn blocking_operation():
    # Can call blocking operations
    let result = await some_future
    return result

fn normal_operation():
    # Can call waitless functions
    let result = fast_operation(21)
    # Can also do blocking operations
    let data = read_file("data.txt")
```

## Features Implemented

- [x] `waitless` function annotation
- [x] `async` function annotation
- [x] Effect checking at runtime
- [x] Prevent blocking calls in waitless functions
- [x] Blocking operations list: recv, join, await, sleep, read_file, write_file, print, println, input
- [ ] Prevent GC allocation in waitless functions (future enhancement)
- [ ] Effect inference (future enhancement)
- [ ] Effect polymorphism (future enhancement)

## Implementation Details

### Parser Changes
- Added `parse_async_function()` and `parse_waitless_function()` methods
- Updated `parse_item()` and `parse_pub_item()` to handle `TokenKind::Async` and `TokenKind::Waitless`
- Functions can be annotated with `async fn` or `waitless fn`

### Runtime Effect Checking
- Added `CURRENT_EFFECT` thread-local to track current effect context
- Added `BLOCKING_OPERATIONS` list of operations that cannot be called from waitless context
- Added `check_waitless_violation()` function that errors if blocking op called in waitless fn
- Modified `exec_function()` to save/restore effect context during function calls

### Blocking Operations
The following operations are blocked in waitless functions:
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
When a blocking operation is used in a waitless function:
```
semantic: blocking operation 'print' not allowed in waitless function
```

## Tests

- `interpreter_waitless_basic` - Waitless fn can do non-blocking computation
- `interpreter_waitless_blocks_print` - Waitless fn cannot use print
- `interpreter_waitless_blocks_await` - Waitless fn cannot use await
- `interpreter_async_fn_basic` - Async fn can use blocking operations
- `interpreter_waitless_can_call_waitless` - Waitless fn can call other waitless fns

## Related

- #30 Actors (Implemented)
- #31 Concurrency Primitives (Implemented)
- #33 Stackless Coroutines (Pending)
