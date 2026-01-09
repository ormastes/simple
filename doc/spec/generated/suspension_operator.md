# Suspension Operator (`~`) Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/suspension_operator_spec.spl`
> **Generated:** 2026-01-09 04:37:07
>
> To update this file, edit the source _spec.spl file and run:
> ```bash
> python scripts/spec_gen.py --input tests/specs/suspension_operator_spec.spl
> ```

**Status:** Draft
**Feature IDs:** #270-275
**Keywords:** async, suspension, await, effects, concurrency
**Last Updated:** 2026-01-05
**Topics:** concurrency, syntax, effects

## Overview

The `~` operator marks expressions that may suspend (perform async operations). It appears in three contexts:

| Context | Syntax | Meaning |
|---------|--------|---------|
| Assignment | `x ~= expr` | Evaluate `expr` (may suspend), assign result to `x` |
| If guard | `if~ cond:` | Evaluate `cond` (may suspend), branch on result |
| While guard | `while~ cond:` | Evaluate `cond` each iteration (may suspend) |

---

## Related Specifications

- **Async Default** - Async-by-default function model
- **Concurrency** - Async/await, futures, actors
- **Syntax** - Core language syntax
- **Functions** - Function definitions and effects

---

## Test Cases (24 total)

| Test | Section | Description |
|------|---------|-------------|
| [motivation_1](#test-1) | Motivation |  |
| [syntax_2](#test-2) | Syntax |  |
| [syntax_3](#test-3) | Syntax |  |
| [syntax_4](#test-4) | Syntax |  |
| [syntax_5](#test-5) | Syntax |  |
| [fetch_data](#test-6) | Effect System Integration |  |
| [good_async](#test-7) | Effect System Integration |  |
| [wrapper](#test-8) | Effect System Integration |  |
| [interaction_with_existing_constructs_9](#test-9) | Interaction with Existing Constructs |  |
| [load_config](#test-10) | Interaction with Existing Constructs |  |
| [interaction_with_existing_constructs_11](#test-11) | Interaction with Existing Constructs |  |
| [interaction_with_existing_constructs_12](#test-12) | Interaction with Existing Constructs |  |
| [get_user](#test-13) | Examples |  |
| [wait_for_ready](#test-14) | Examples |  |
| [fetch_and_merge](#test-15) | Examples |  |
| [smart_fetch](#test-16) | Examples |  |
| [process_stream](#test-17) | Examples |  |
| [examples_18](#test-18) | Examples |  |
| [compound_suspending_assignment_19](#test-19) | Compound Suspending Assignment |  |
| [chained_suspending_conditions_20](#test-20) | Chained Suspending Conditions |  |
| [implementation_notes_21](#test-21) | Implementation Notes |  |
| [implementation_notes_22](#test-22) | Implementation Notes |  |
| [migration_guide_23](#test-23) | Migration Guide |  |
| [migration_guide_24](#test-24) | Migration Guide |  |

---

### Test 1: Motivation

**Test name:** `motivation_1`

**Code:**

```simple
test "motivation_1":
    """
    Motivation
    """
    # Problem: Is this condition suspending? Hard to tell at a glance.
    if fetch_status() == Ready:
        proceed()

    while not server.is_up():   # Does this suspend each iteration?
        retry()
    assert_compiles()
```

### Test 2: Syntax

**Test name:** `syntax_2`

**Code:**

```simple
test "syntax_2":
    """
    Syntax
    """
    # Basic suspending assignment
    let user: User ~= fetch_user(id)

    # Type inference works
    let data ~= load_data()

    # Mutable variable
    let mut counter ~= get_initial_count()
    counter ~= refresh_count()

    # Discard result (await and ignore)
    _ ~= timer.sleep(100_ms)
    assert_compiles()
```

### Test 3: Syntax

**Test name:** `syntax_3`

**Code:**

```simple
test "syntax_3":
    """
    Syntax
    """
    # Suspending condition
    if~ is_server_ready():
        start_processing()
    elif~ fallback_available():
        use_fallback()
    else:
        fail()

    # Multiple conditions (all may suspend)
    if~ check_auth() and~ has_permission():
        allow()
    assert_compiles()
```

### Test 4: Syntax

**Test name:** `syntax_4`

**Code:**

```simple
test "syntax_4":
    """
    Syntax
    """
    # Poll until ready
    while~ not is_ready():
        _ ~= timer.sleep(100_ms)
        log("Waiting...")

    # Process stream
    while~ let Some(item) = stream.next():
        process(item)
    assert_compiles()
```

### Test 5: Syntax

**Test name:** `syntax_5`

**Code:**

```simple
test "syntax_5":
    """
    Syntax
    """
    # Async iterator
    for~ item in async_stream():
        process(item)

    # Equivalent to:
    while~ let Some(item) = async_stream.next():
        process(item)
    assert_compiles()
```

### Test 6: Effect System Integration

**Test name:** `fetch_data`

**Code:**

```simple
fn fetch_data() -> Data:
    let response ~= http.get(url)
    return parse(response)

# Explicitly async
async fn process() -> Result:
    ...
```

### Test 7: Effect System Integration

**Test name:** `good_async`

**Code:**

```simple
fn good_async():
    let x ~= fetch()    # OK: fn allows suspension

actor Counter:
    on Increment(n: i64) async:
        let x ~= fetch()    # ERROR: actor handlers are run-to-completion
```

### Test 8: Effect System Integration

**Test name:** `wrapper`

**Code:**

```simple
fn wrapper() -> Data:
    let x ~= inner_fetch()   # wrapper is now suspending
    return x

sync fn caller():
    let d = wrapper()        # ERROR: calling suspending fn from sync
```

### Test 9: Interaction with Existing Constructs

**Test name:** `interaction_with_existing_constructs_9`

**Code:**

```simple
test "interaction_with_existing_constructs_9":
    """
    Interaction with Existing Constructs
    """
    # These are equivalent:
    let x ~= fetch_data()
    let x = await fetch_data()

    # But ~= allows type-driven behavior:
    let x: Data ~= maybe_future()   # Works if maybe_future returns Data or Future[Data]
    assert_compiles()
```

### Test 10: Interaction with Existing Constructs

**Test name:** `load_config`

**Code:**

```simple
fn load_config() -> Result[Config, Error]:
    # Suspend, then propagate error
    let content ~= read_file(path)?

    # Equivalent to:
    let content = await read_file(path)?

    # Or explicitly:
    let future = read_file(path)
    let result = await future
    let content = result?

    return parse(content)
```

### Test 11: Interaction with Existing Constructs

**Test name:** `interaction_with_existing_constructs_11`

**Code:**

```simple
test "interaction_with_existing_constructs_11":
    """
    Interaction with Existing Constructs
    """
    # Suspending pattern match in while
    while~ let Some(msg) = channel.recv():
        handle(msg)

    # Suspending match expression
    match~ fetch_status():
        case Ready: proceed()
        case Pending: wait()
        case Error(e): fail(e)
    assert_compiles()
```

### Test 12: Interaction with Existing Constructs

**Test name:** `interaction_with_existing_constructs_12`

**Code:**

```simple
test "interaction_with_existing_constructs_12":
    """
    Interaction with Existing Constructs
    """
    # Traditional combinator style (still valid)
    let result = fetch_a()
        .then(\a: fetch_b(a))
        .then(\b: process(b))
        .catch(\e: handle_error(e))

    # With suspension operator (imperative style)
    let a ~= fetch_a()
    let b ~= fetch_b(a)
    let result ~= process(b)
    assert_compiles()
```

### Test 13: Examples

**Test name:** `get_user`

**Code:**

```simple
fn get_user(id: UserId) -> Result[User, HttpError]:
    let response ~= http.get("/users/{id}")?
    let user: User ~= response.json()?
    return Ok(user)
```

### Test 14: Examples

**Test name:** `wait_for_ready`

**Code:**

```simple
fn wait_for_ready(timeout: Duration) -> Result[(), TimeoutError]:
    let deadline = now() + timeout

    while~ not is_ready():
        if now() > deadline:
            return Err(TimeoutError("Timed out waiting for ready"))
        _ ~= timer.sleep(100_ms)

    return Ok(())
```

### Test 15: Examples

**Test name:** `fetch_and_merge`

**Code:**

```simple
fn fetch_and_merge(ids: [UserId]) -> [User]:
    # Start all fetches in parallel
    let futures = ids.map(\id: fetch_user(id))

    # Wait for all (suspends once)
    let users ~= Future.all(futures)

    return users
```

### Test 16: Examples

**Test name:** `smart_fetch`

**Code:**

```simple
fn smart_fetch(id: UserId, use_cache: bool) -> User:
    if use_cache:
        # Non-suspending path
        if let Some(user) = cache.get(id):
            return user

    # Suspending path
    let user ~= fetch_from_server(id)
    cache.set(id, user)
    return user
```

### Test 17: Examples

**Test name:** `process_stream`

**Code:**

```simple
fn process_stream(stream: AsyncStream[Message]) -> Stats:
    let mut stats = Stats.new()

    for~ msg in stream:
        match msg:
            case Data(payload):
                stats.record(payload)
            case Heartbeat:
                _ ~= send_ack()
            case Close:
                break

    return stats
```

### Test 18: Examples

**Test name:** `examples_18`

**Code:**

```simple
test "examples_18":
    """
    Examples
    """
    # Actors cannot use ~ directly, but can spawn futures
    actor DataService:
        state:
            cache: Dict[Key, Value] = {}

        on Query(key: Key, reply_to: Pid[Value]) async:
            if key in self.cache:
                send reply_to, self.cache[key]
            else:
                # Spawn async task (not blocking the actor)
                spawn_task:
                    let value ~= fetch_remote(key)
                    send self, CacheAndReply(key, value, reply_to)

        on CacheAndReply(key: Key, value: Value, reply_to: Pid[Value]) async:
            self.cache[key] = value
            send reply_to, value
    assert_compiles()
```

### Test 19: Compound Suspending Assignment

**Test name:** `compound_suspending_assignment_19`

**Code:**

```simple
test "compound_suspending_assignment_19":
    """
    Compound Suspending Assignment
    """
    # Suspending compound assignment
    counter ~+= fetch_increment()    # counter = counter + (await fetch_increment())

    # All compound operators have suspending variants
    value ~-= get_decrement()
    total ~*= get_multiplier()
    quota ~/= get_divisor()
    remainder ~%= get_modulo()
    assert_compiles()
```

### Test 20: Chained Suspending Conditions

**Test name:** `chained_suspending_conditions_20`

**Code:**

```simple
test "chained_suspending_conditions_20":
    """
    Chained Suspending Conditions
    """
    # Both conditions may suspend
    if~ check_auth() and~ has_permission():
        allow()

    # First suspends, second is sync
    if~ is_online() and is_valid(token):
        proceed()

    # Short-circuit: second only evaluated if first is true
    if~ expensive_check() and~ another_expensive_check():
        ...
    assert_compiles()
```

### Test 21: Implementation Notes

**Test name:** `implementation_notes_21`

**Code:**

```simple
test "implementation_notes_21":
    """
    Implementation Notes
    """
    # Source
    let x ~= expr

    # Desugared
    let __tmp = expr
    let x = if __tmp is Future:
        await __tmp
    else:
        __tmp
    assert_compiles()
```

### Test 22: Implementation Notes

**Test name:** `implementation_notes_22`

**Code:**

```simple
test "implementation_notes_22":
    """
    Implementation Notes
    """
    # Source
    if~ cond:
        body

    # Desugared
    let __cond = cond
    let __resolved = if __cond is Future:
        await __cond
    else:
        __cond
    if __resolved:
        body
    assert_compiles()
```

### Test 23: Migration Guide

**Test name:** `migration_guide_23`

**Code:**

```simple
test "migration_guide_23":
    """
    Migration Guide
    """
    # Before
    let x = await fetch()
    if await is_ready():
        ...

    # After (both valid, choose by preference)
    let x ~= fetch()
    if~ is_ready():
        ...
    assert_compiles()
```

### Test 24: Migration Guide

**Test name:** `migration_guide_24`

**Code:**

```simple
test "migration_guide_24":
    """
    Migration Guide
    """
    # Before (implicit await when assigning Future to non-Future type)
    let x: Data = fetch()   # Implicitly awaited

    # After (explicit suspension)
    let x: Data ~= fetch()  # Explicitly suspending
    assert_compiles()
```

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/suspension_operator_spec.spl`*
