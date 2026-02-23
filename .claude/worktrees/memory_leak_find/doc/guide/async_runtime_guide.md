# Simple Async Runtime - User Guide
**Version**: 0.5.0-alpha  
**Status**: Phase 1 Complete (Pure Simple SFFI)

## Quick Start

### Task ID Allocation (Works Now!)

```simple
use std.async_sffi (task_alloc_id, NEXT_TASK_ID)

fn main():
    val id1 = task_alloc_id()
    val id2 = task_alloc_id()
    val id3 = task_alloc_id()
    
    print "IDs: {id1}, {id2}, {id3}"
    print "Next: {NEXT_TASK_ID}"
```

### Waker System (Works Now!)

```simple
use std.async_sffi (waker_signal, waker_check, waker_clear)

fn main():
    waker_signal(0, 5)           # Signal task 5
    print waker_check(5)         # true
    waker_clear(5)              # Clear
    print waker_check(5)         # false
```

## Core Concepts

### Poll Type
```simple
enum Poll<T>:
    Ready(value: T)    # Completed
    Pending            # Not ready
```

### Priority Levels
```simple
enum Priority:
    Critical  # 0 - Highest
    High      # 1
    Normal    # 2 - Default
    Low       # 3
    Idle      # 4 - Background
```

## API Reference - async_sffi.spl

### Module-Level State
```simple
pub var NEXT_TASK_ID: usize        # Task ID counter
pub var WAKER_REGISTRY: [bool]     # 64-task wake flags
```

### Functions

**task_alloc_id() -> usize**  
Allocate unique task ID (0, 1, 2, ...)

**task_reset_counter()**  
Reset counter to 0 (for testing)

**waker_signal(scheduler_ref: usize, task_id: usize)**  
Signal task wake (task_id < 64)

**waker_check(task_id: usize) -> bool**  
Check if task has wake pending

**waker_clear(task_id: usize)**  
Clear wake signal

**waker_reset()**  
Clear all wake signals

## Runtime Selection

### Embedded Runtime
- Fixed capacity: 16 tasks, 32 futures
- No heap allocation
- Cooperative scheduling
- Use for: Microcontrollers, bare-metal

### Host Runtime
- Dynamic capacity
- Work-stealing scheduler
- Full waker callbacks
- Use for: Servers, desktop apps

## Performance

### SFFI Waker System
- **Capacity**: 64 tasks max
- **Operations**: O(1) signal/check/clear
- **Memory**: 64 bytes (1 byte per task)
- **Limitation**: Polling only, no callbacks

### Embedded Runtime
- **Memory**: ~1 KB (16 tasks)
- **CPU**: O(1) operations
- **Optimization**: Keep tasks small, poll frequently

### Host Runtime
- **Memory**: ~8 KB + (128 bytes × task count)
- **CPU**: O(log N) work-stealing
- **Optimization**: Batch spawning, avoid excess tasks

## Advanced Patterns

### Batch Operations
```simple
fn signal_batch(tasks: [usize]):
    var i = 0
    while i < tasks.len():
        waker_signal(0, tasks[i])
        i = i + 1

fn check_batch(tasks: [usize]) -> [bool]:
    var results = []
    var i = 0
    while i < tasks.len():
        results.push(waker_check(tasks[i]))
        i = i + 1
    results
```

## Examples

**Working test**: `/tmp/async_simple_test.spl`  
**Full report**: `doc/report/async_runtime_implementation_2026-02-05.md`

## Roadmap

- ✅ Phase 1: Pure Simple SFFI (Complete)
- ⏳ Phase 2: SSpec test execution (Pending)
- ⏳ Phase 3: Function fields support (Pending)
- 🔮 Phase 4: async/await syntax (Future)
