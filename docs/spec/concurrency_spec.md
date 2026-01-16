# Isolated Threads and Go-style Concurrency

*Source: `simple/std_lib/test/features/language/concurrency_spec.spl`*

---

# Isolated Threads and Go-style Concurrency

**Feature ID:** Concurrency
**Category:** Language - Concurrency
**Difficulty:** 4/5
**Status:** Planned (Phase 1-3)

## Overview

Simple provides safe concurrent programming through **isolated threads** - threads
that cannot share mutable state. All data passed to threads is deep-copied, and
communication happens exclusively through channels.

This design **prevents data races by construction**, unlike Go which relies on
runtime race detection.

## Core Principles

1. **No shared mutable state** - Cannot access mutable globals from threads
2. **Copy or const only** - Data must be deep-copied or immutable
3. **Channel-only communication** - Channels are the only inter-thread mechanism
4. **Global const access** - Can read global constants

## Syntax

**Current (spawn_isolated):**
```simple
val handle = spawn_isolated(data) \\d: d.sum()
val handle = spawn_isolated2(data, ch) \\d, c: c.send(d.sum())
```

**Proposed (go keyword - two styles):**
```simple
# Style A: Rust-style capture with pipes (LL(1) safe)
val handle = go |data| \\: data.sum()
val handle = go |data, ch| \\: ch.send(data.sum())

# Style B: Current style with go keyword (LL(1) safe)
val handle = go(data) \\d: d.sum()
val handle = go(data, ch) \\d, c: c.send(d.sum())
```

## Safety Guarantee

Go allows data races:
```go
var counter int
go func() { counter++ }()  // RACE CONDITION!
```

Simple prevents by design:
```simple
var counter = 0
go |counter| \\:           # counter is COPIED
    counter += 1           # modifies local copy only
# counter is still 0 - no race, but also no effect!
```

## Key Features

- **Data Isolation:** All data passed to threads is deep-copied
- **Channel Communication:** Type-safe channels for message passing
- **ThreadHandle:** Join, check completion, get results
- **Parallel Primitives:** parallel_map, parallel_reduce for data parallelism

## Implementation

**Primary Files:**
- `simple/std_lib/src/concurrency/threads.spl` - Thread API
- `simple/std_lib/src/concurrency/channels.spl` - Channel types
- `src/runtime/src/value/channels.rs` - Channel FFI

**Dependencies:**
- Feature: Closures (lambda capture)
- Feature: Channels (communication)

## Test Coverage

This specification validates:
1. **Thread Spawning:** Creating isolated threads with data
2. **Data Isolation:** Verifying copies are independent
3. **Thread Join:** Waiting for completion and getting results
4. **Parallel Operations:** parallel_map, parallel_reduce

## spawn_isolated Function

    The `spawn_isolated` function creates a new OS thread with isolated data.
    All data passed is deep-copied to prevent shared mutable state.

    **Syntax:**
    ```simple
    val handle = spawn_isolated(data) \\copied_data: expression
    ```

    **Key Properties:**
    - Data is deep-copied into the thread
    - No shared mutable state possible
    - Returns ThreadHandle for joining
    - Closure executes in separate OS thread

    **Safety:** This design prevents data races by construction.

**Given** data to pass to a thread
        **When** spawning with spawn_isolated
        **Then** thread receives a deep copy of the data

        **Example:**
        ```simple
        val data = [1, 2, 3]
        val handle = spawn_isolated(data) \\d:
            d.sum()
        val result = handle.join()
        # result = 6
        ```

        **Data Isolation:**
        - `data` in main thread is unchanged
        - `d` in spawned thread is independent copy
        - Mutations to `d` don't affect `data`

        **Verification:** Thread computes sum of copied data correctly

        **Implementation:** See threads.spl::spawn_isolated()

**Given** multiple data values to pass
        **When** spawning with spawn_isolated2
        **Then** both values are copied to the thread

        **Example:**
        ```simple
        val nums = [1, 2, 3]
        val multiplier = 2
        val handle = spawn_isolated2(nums, multiplier) \\n, m:
            n.map(\\x: x * m).sum()
        val result = handle.join()
        # result = 12 (2 + 4 + 6)
        ```

        **Use Case:** Pass data and configuration separately

        **Verification:** Thread uses both copied values correctly

## Go Keyword for Thread Spawning

    The `go` keyword provides concise syntax for spawning threads,
    inspired by Go but maintaining Simple's safety guarantees.

    **Two Styles (both LL(1) compatible):**

    **Style A - Capture list:**
    ```simple
    go |data| \\: data.sum()
    go |data, ch| \\: ch.send(data.sum())
    ```

    **Style B - Parameter passing:**
    ```simple
    go(data) \\d: d.sum()
    go(data, ch) \\d, c: c.send(d.sum())
    ```

    **Key Difference from Go:**
    - All captured/passed data is deep-copied
    - No implicit capture of mutable references
    - Channel references are safe (sync primitives)

**Given** data to capture in thread
        **When** using go |captures| syntax
        **Then** captured values are deep-copied

        **Proposed Syntax:**
        ```simple
        val data = [1, 2, 3]
        val handle = go |data| \\: data.sum()
        ```

        **LL(1) Analysis:**
        - `go` keyword starts statement
        - `|` pipe starts capture list (unambiguous)
        - `\\:` starts lambda body

        **Verification:** Syntax is LL(1) compatible

**Given** data to pass to thread
        **When** using go(args) syntax
        **Then** arguments are copied and bound to parameters

        **Proposed Syntax:**
        ```simple
        val data = [1, 2, 3]
        val handle = go(data) \\d: d.sum()
        ```

        **LL(1) Analysis:**
        - `go` keyword starts statement
        - `(` starts argument list (unambiguous)
        - `\\d:` starts lambda with parameter

        **Verification:** Syntax is LL(1) compatible

## ThreadHandle API

    ThreadHandle provides methods to interact with spawned threads:
    - `join()` - Wait for completion, get result
    - `is_done()` - Non-blocking completion check
    - `id()` - Get thread ID
    - `free()` - Release handle resources

    **Pattern:**
    ```simple
    val handle = spawn_isolated(data) \\d: compute(d)

    # Option 1: Block until done
    val result = handle.join()

    # Option 2: Poll completion
    while not handle.is_done():
        do_other_work()
    val result = handle.join()
    ```

**Given** a spawned thread computing a value
        **When** calling join() on the handle
        **Then** blocks until thread completes and returns result

        **Example:**
        ```simple
        val handle = spawn_isolated(42) \\x: x * 2
        val result = handle.join()
        # result = 84
        ```

        **Join Semantics:**
        - Blocks calling thread until spawned thread exits
        - Returns the value from the thread's lambda
        - Can only join once per handle

        **Verification:** Join returns computed result

**Given** a spawned thread
        **When** calling is_done() on the handle
        **Then** returns true if thread completed, false otherwise

        **Non-Blocking Check:**
        ```simple
        val handle = spawn_isolated(data) \\d: slow_compute(d)

        while not handle.is_done():
            print("Still computing...")
            sleep(100)

        val result = handle.join()
        ```

        **Use Case:** Progress monitoring, timeouts

        **Verification:** is_done() correctly reports completion status

## Data Parallelism Primitives

    Simple provides high-level parallel operations built on isolated threads:
    - `parallel_map` - Transform elements in parallel
    - `parallel_reduce` - Aggregate elements in parallel

    **parallel_map:**
    ```simple
    val results = parallel_map(items, \\x: x * 2, num_threads)
    ```

    **parallel_reduce:**
    ```simple
    val sum = parallel_reduce(items, \\a, b: a + b, 0, num_threads)
    ```

    **Automatic Chunking:**
    - Divides work into chunks based on thread count
    - Each thread processes its chunk independently
    - Results combined in order

**Given** a list of elements and a transformation function
        **When** calling parallel_map with thread count
        **Then** applies transformation in parallel, returns results in order

        **Example:**
        ```simple
        val data = [1, 2, 3, 4, 5, 6, 7, 8]
        val doubled = parallel_map(data, \\x: x * 2, 4)
        # doubled = [2, 4, 6, 8, 10, 12, 14, 16]
        ```

        **How It Works:**
        1. Divide data into 4 chunks: [[1,2], [3,4], [5,6], [7,8]]
        2. Spawn 4 threads, each maps its chunk
        3. Collect results in order
        4. Return flattened result list

        **Thread Safety:** Each thread works on independent copy

        **Verification:** Results match sequential map

**Given** a list, reducer function, and initial value
        **When** calling parallel_reduce with thread count
        **Then** reduces in parallel and combines partial results

        **Example:**
        ```simple
        val data = [1, 2, 3, 4, 5, 6, 7, 8]
        val sum = parallel_reduce(data, \\a, b: a + b, 0, 4)
        # sum = 36
        ```

        **How It Works:**
        1. Divide into chunks: [[1,2], [3,4], [5,6], [7,8]]
        2. Each thread reduces its chunk: [3, 7, 11, 15]
        3. Main thread combines: 3 + 7 + 11 + 15 = 36

        **Associativity Requirement:**
        Reducer must be associative for correct parallel results:
        - ✅ `a + b` (addition is associative)
        - ✅ `a * b` (multiplication is associative)
        - ❌ `a - b` (subtraction is NOT associative)

        **Verification:** Result matches sequential reduce

## par() Method for Parallel Iteration

    Proposed extension to List for Ruby-style parallel method chaining:

    ```simple
    val results = items
        .par()                    # Convert to parallel iterator
        .map \\x: x * 2           # Parallel map
        .filter \\x: x > 10       # Parallel filter
        .collect()                # Collect results

    # Or fluent style
    val results = items.par().map(\\x: x * 2).collect()
    ```

    **Methods:**
    - `par()` - Create parallel iterator
    - `threads(n)` - Set thread count
    - `map(f)` - Parallel transform
    - `filter(p)` - Parallel filter
    - `reduce(f, init)` - Parallel reduce
    - `collect()` - Gather results

**Given** a list and transformation
        **When** using par().map() chain
        **Then** transforms elements in parallel

        **Proposed Syntax:**
        ```simple
        val doubled = [1, 2, 3, 4].par().map \\x: x * 2
        # doubled = [2, 4, 6, 8]
        ```

        **LL(1) Analysis:**
        - `.par()` is normal method call
        - `.map` is method call
        - `\\x:` starts lambda (backslash unambiguous)

        **Verification:** Results match sequential map

**Given** a parallel iterator
        **When** calling threads(n)
        **Then** uses specified thread count

        **Proposed Syntax:**
        ```simple
        val results = data
            .par()
            .threads(8)           # Use 8 threads
            .map \\x: heavy_compute(x)
            .collect()
        ```

        **Default:** Uses available_parallelism() if not specified

        **Verification:** Thread count is configurable
