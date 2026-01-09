# Suspension Operator (`~`) Specification

> **⚠️ GENERATED FILE** - Do not edit directly!
> **Source:** `tests/specs/suspension_operator_spec.spl`
> **Generated:** 2026-01-09 06:15:42
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

## Quick Navigation

- [Overview](#overview)
- [Symbols Reference](#symbols-reference)
- [Test Cases](#test-cases) (24 tests)
- [Source Code](#source-code)

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

## Symbols Reference

| Symbol | Used in Tests |
|--------|---------------|
| `Actors` | [18](#examples_18) |
| `After` | [23](#migration_guide_23), [24](#migration_guide_24) |
| `All` | [19](#compound_suspending_assignment_19) |
| `And` | [15](#fetch_and_merge) |
| `Assignment` | [19](#compound_suspending_assignment_19) |
| `Async` | [5](#syntax_5), [7](#good_async) |
| `AsyncStream` | [17](#process_stream) |
| `Basic` | [2](#syntax_2) |
| `Before` | [23](#migration_guide_23), [24](#migration_guide_24) |
| `Both` | [20](#chained_suspending_conditions_20) |
| `But` | [9](#interaction_with_existing_constructs_9) |
| `CacheAndReply` | [18](#examples_18) |
| `Chained` | [20](#chained_suspending_conditions_20) |
| `ChainedSuspendingConditions` | [20](#chained_suspending_conditions_20) |
| `Close` | [17](#process_stream) |
| `Compound` | [19](#compound_suspending_assignment_19) |
| `CompoundSuspendingAssignment` | [19](#compound_suspending_assignment_19) |
| `Conditions` | [20](#chained_suspending_conditions_20) |
| `Config` | [10](#load_config) |
| `Constructs` | [9](#interaction_with_existing_constructs_9), [11](#interaction_with_existing_constructs_11), [12](#interaction_with_existing_constructs_12) |
| `Counter` | [7](#good_async) |
| `Data` | [6](#fetch_data), [8](#wrapper), [9](#interaction_with_existing_constructs_9), [17](#process_stream), [24](#migration_guide_24) |
| `DataService` | [18](#examples_18) |
| `Desugared` | [21](#implementation_notes_21), [22](#implementation_notes_22) |
| `Dict` | [18](#examples_18) |
| `Discard` | [2](#syntax_2) |
| `Does` | [1](#motivation_1) |
| `Duration` | [14](#wait_for_ready) |
| `ERROR` | [7](#good_async), [8](#wrapper) |
| `Equivalent` | [5](#syntax_5), [10](#load_config) |
| `Err` | [14](#wait_for_ready) |
| `Error` | [10](#load_config), [11](#interaction_with_existing_constructs_11) |
| `Examples` | [18](#examples_18) |
| `Existing` | [9](#interaction_with_existing_constructs_9), [11](#interaction_with_existing_constructs_11), [12](#interaction_with_existing_constructs_12) |
| `Explicitly` | [6](#fetch_data), [24](#migration_guide_24) |
| `Fetch` | [6](#fetch_data), [15](#fetch_and_merge), [16](#smart_fetch) |
| `FetchAndMerge` | [15](#fetch_and_merge) |
| `FetchData` | [6](#fetch_data) |
| `First` | [20](#chained_suspending_conditions_20) |
| `For` | [14](#wait_for_ready) |
| `Future` | [9](#interaction_with_existing_constructs_9), [15](#fetch_and_merge), [21](#implementation_notes_21), [22](#implementation_notes_22), [24](#migration_guide_24) |
| `Get` | [13](#get_user) |
| `GetUser` | [13](#get_user) |
| `Good` | [7](#good_async) |
| `GoodAsync` | [7](#good_async) |
| `Guide` | [23](#migration_guide_23), [24](#migration_guide_24) |
| `Hard` | [1](#motivation_1) |
| `Heartbeat` | [17](#process_stream) |
| `HttpError` | [13](#get_user) |
| `Implementation` | [21](#implementation_notes_21), [22](#implementation_notes_22) |
| `ImplementationNotes` | [21](#implementation_notes_21), [22](#implementation_notes_22) |
| `Implicitly` | [24](#migration_guide_24) |
| `Increment` | [7](#good_async) |
| `Interaction` | [9](#interaction_with_existing_constructs_9), [11](#interaction_with_existing_constructs_11), [12](#interaction_with_existing_constructs_12) |
| `InteractionWithExistingConstructs` | [9](#interaction_with_existing_constructs_9), [11](#interaction_with_existing_constructs_11), [12](#interaction_with_existing_constructs_12) |
| `Key` | [18](#examples_18) |
| `Load` | [10](#load_config) |
| `LoadConfig` | [10](#load_config) |
| `Merge` | [15](#fetch_and_merge) |
| `Message` | [17](#process_stream) |
| `Migration` | [23](#migration_guide_23), [24](#migration_guide_24) |
| `MigrationGuide` | [23](#migration_guide_23), [24](#migration_guide_24) |
| `Motivation` | [1](#motivation_1) |
| `Multiple` | [3](#syntax_3) |
| `Mutable` | [2](#syntax_2) |
| `Non` | [16](#smart_fetch) |
| `Notes` | [21](#implementation_notes_21), [22](#implementation_notes_22) |
| `Pending` | [11](#interaction_with_existing_constructs_11) |
| `Pid` | [18](#examples_18) |
| `Poll` | [4](#syntax_4) |
| `Problem` | [1](#motivation_1) |
| `Process` | [4](#syntax_4), [17](#process_stream) |
| `ProcessStream` | [17](#process_stream) |
| `Query` | [18](#examples_18) |
| `Ready` | [1](#motivation_1), [11](#interaction_with_existing_constructs_11), [14](#wait_for_ready) |
| `Result` | [6](#fetch_data), [10](#load_config), [13](#get_user), [14](#wait_for_ready) |
| `Short` | [20](#chained_suspending_conditions_20) |
| `Smart` | [16](#smart_fetch) |
| `SmartFetch` | [16](#smart_fetch) |
| `Source` | [21](#implementation_notes_21), [22](#implementation_notes_22) |
| `Spawn` | [18](#examples_18) |
| `Start` | [15](#fetch_and_merge) |
| `Stats` | [17](#process_stream) |
| `Stream` | [17](#process_stream) |
| `Suspend` | [10](#load_config) |
| `Suspending` | [3](#syntax_3), [11](#interaction_with_existing_constructs_11), [16](#smart_fetch), [19](#compound_suspending_assignment_19), [20](#chained_suspending_conditions_20) |
| `Syntax` | [2](#syntax_2), [3](#syntax_3), [4](#syntax_4), [5](#syntax_5) |
| `These` | [9](#interaction_with_existing_constructs_9) |
| `Timed` | [14](#wait_for_ready) |
| `TimeoutError` | [14](#wait_for_ready) |
| `Traditional` | [12](#interaction_with_existing_constructs_12) |
| `Type` | [2](#syntax_2) |
| `User` | [2](#syntax_2), [13](#get_user), [15](#fetch_and_merge), [16](#smart_fetch) |
| `UserId` | [13](#get_user), [15](#fetch_and_merge), [16](#smart_fetch) |
| `Value` | [18](#examples_18) |
| `Wait` | [14](#wait_for_ready), [15](#fetch_and_merge) |
| `WaitForReady` | [14](#wait_for_ready) |
| `Waiting` | [4](#syntax_4) |
| `With` | [9](#interaction_with_existing_constructs_9), [11](#interaction_with_existing_constructs_11), [12](#interaction_with_existing_constructs_12) |
| `Works` | [9](#interaction_with_existing_constructs_9) |
| `Wrapper` | [8](#wrapper) |
| `all` | [15](#fetch_and_merge) |
| `allow` | [3](#syntax_3), [20](#chained_suspending_conditions_20) |
| `and` | [15](#fetch_and_merge) |
| `another_expensive_check` | [20](#chained_suspending_conditions_20) |
| `assert_compiles` | [1](#motivation_1), [2](#syntax_2), [3](#syntax_3), [4](#syntax_4), [5](#syntax_5), ... (15 total) |
| `assignment` | [19](#compound_suspending_assignment_19) |
| `async` | [7](#good_async) |
| `async_stream` | [5](#syntax_5) |
| `caller` | [8](#wrapper) |
| `catch` | [12](#interaction_with_existing_constructs_12) |
| `chained` | [20](#chained_suspending_conditions_20) |
| `chained_suspending_conditions` | [20](#chained_suspending_conditions_20) |
| `check_auth` | [3](#syntax_3), [20](#chained_suspending_conditions_20) |
| `compound` | [19](#compound_suspending_assignment_19) |
| `compound_suspending_assignment` | [19](#compound_suspending_assignment_19) |
| `conditions` | [3](#syntax_3), [20](#chained_suspending_conditions_20) |
| `config` | [10](#load_config) |
| `constructs` | [9](#interaction_with_existing_constructs_9), [11](#interaction_with_existing_constructs_11), [12](#interaction_with_existing_constructs_12) |
| `data` | [6](#fetch_data) |
| `examples` | [18](#examples_18) |
| `existing` | [9](#interaction_with_existing_constructs_9), [11](#interaction_with_existing_constructs_11), [12](#interaction_with_existing_constructs_12) |
| `expensive_check` | [20](#chained_suspending_conditions_20) |
| `fail` | [3](#syntax_3), [11](#interaction_with_existing_constructs_11) |
| `fallback_available` | [3](#syntax_3) |
| `fetch` | [6](#fetch_data), [7](#good_async), [15](#fetch_and_merge), [16](#smart_fetch), [23](#migration_guide_23), ... (6 total) |
| `fetch_a` | [12](#interaction_with_existing_constructs_12) |
| `fetch_and_merge` | [15](#fetch_and_merge) |
| `fetch_b` | [12](#interaction_with_existing_constructs_12) |
| `fetch_data` | [6](#fetch_data), [9](#interaction_with_existing_constructs_9) |
| `fetch_from_server` | [16](#smart_fetch) |
| `fetch_increment` | [19](#compound_suspending_assignment_19) |
| `fetch_remote` | [18](#examples_18) |
| `fetch_status` | [1](#motivation_1), [11](#interaction_with_existing_constructs_11) |
| `fetch_user` | [2](#syntax_2), [15](#fetch_and_merge) |
| `for` | [14](#wait_for_ready) |
| `get` | [6](#fetch_data), [13](#get_user), [16](#smart_fetch) |
| `get_decrement` | [19](#compound_suspending_assignment_19) |
| `get_divisor` | [19](#compound_suspending_assignment_19) |
| `get_initial_count` | [2](#syntax_2) |
| `get_modulo` | [19](#compound_suspending_assignment_19) |
| `get_multiplier` | [19](#compound_suspending_assignment_19) |
| `get_user` | [13](#get_user) |
| `good` | [7](#good_async) |
| `good_async` | [7](#good_async) |
| `guide` | [23](#migration_guide_23), [24](#migration_guide_24) |
| `handle` | [11](#interaction_with_existing_constructs_11) |
| `handle_error` | [12](#interaction_with_existing_constructs_12) |
| `has_permission` | [3](#syntax_3), [20](#chained_suspending_conditions_20) |
| `implementation` | [21](#implementation_notes_21), [22](#implementation_notes_22) |
| `implementation_notes` | [21](#implementation_notes_21), [22](#implementation_notes_22) |
| `inner_fetch` | [8](#wrapper) |
| `interaction` | [9](#interaction_with_existing_constructs_9), [11](#interaction_with_existing_constructs_11), [12](#interaction_with_existing_constructs_12) |
| `interaction_with_existing_constructs` | [9](#interaction_with_existing_constructs_9), [11](#interaction_with_existing_constructs_11), [12](#interaction_with_existing_constructs_12) |
| `is_online` | [20](#chained_suspending_conditions_20) |
| `is_ready` | [4](#syntax_4), [14](#wait_for_ready), [23](#migration_guide_23) |
| `is_server_ready` | [3](#syntax_3) |
| `is_up` | [1](#motivation_1) |
| `is_valid` | [20](#chained_suspending_conditions_20) |
| `json` | [13](#get_user) |
| `load` | [10](#load_config) |
| `load_config` | [10](#load_config) |
| `load_data` | [2](#syntax_2) |
| `log` | [4](#syntax_4) |
| `map` | [15](#fetch_and_merge) |
| `maybe_future` | [9](#interaction_with_existing_constructs_9) |
| `merge` | [15](#fetch_and_merge) |
| `migration` | [23](#migration_guide_23), [24](#migration_guide_24) |
| `migration_guide` | [23](#migration_guide_23), [24](#migration_guide_24) |
| `motivation` | [1](#motivation_1) |
| `new` | [17](#process_stream) |
| `next` | [4](#syntax_4), [5](#syntax_5) |
| `notes` | [21](#implementation_notes_21), [22](#implementation_notes_22) |
| `now` | [14](#wait_for_ready) |
| `operator` | [12](#interaction_with_existing_constructs_12) |
| `parse` | [6](#fetch_data), [10](#load_config) |
| `proceed` | [1](#motivation_1), [11](#interaction_with_existing_constructs_11), [20](#chained_suspending_conditions_20) |
| `process` | [4](#syntax_4), [5](#syntax_5), [6](#fetch_data), [12](#interaction_with_existing_constructs_12), [17](#process_stream) |
| `process_stream` | [17](#process_stream) |
| `read_file` | [10](#load_config) |
| `ready` | [14](#wait_for_ready) |
| `record` | [17](#process_stream) |
| `recv` | [11](#interaction_with_existing_constructs_11) |
| `refresh_count` | [2](#syntax_2) |
| `result` | [2](#syntax_2) |
| `retry` | [1](#motivation_1) |
| `send_ack` | [17](#process_stream) |
| `set` | [16](#smart_fetch) |
| `sleep` | [2](#syntax_2), [4](#syntax_4), [14](#wait_for_ready) |
| `smart` | [16](#smart_fetch) |
| `smart_fetch` | [16](#smart_fetch) |
| `start_processing` | [3](#syntax_3) |
| `stream` | [17](#process_stream) |
| `style` | [12](#interaction_with_existing_constructs_12) |
| `suspending` | [19](#compound_suspending_assignment_19), [20](#chained_suspending_conditions_20) |
| `syntax` | [2](#syntax_2), [3](#syntax_3), [4](#syntax_4), [5](#syntax_5) |
| `task` | [18](#examples_18) |
| `then` | [12](#interaction_with_existing_constructs_12) |
| `use_fallback` | [3](#syntax_3) |
| `user` | [13](#get_user) |
| `wait` | [11](#interaction_with_existing_constructs_11), [14](#wait_for_ready) |
| `wait_for_ready` | [14](#wait_for_ready) |
| `with` | [9](#interaction_with_existing_constructs_9), [11](#interaction_with_existing_constructs_11), [12](#interaction_with_existing_constructs_12) |
| `wrapper` | [8](#wrapper) |

---

## Test Cases (24 total)

| # | Test | Section | Symbols |
|---|------|---------|---------|
| 1 | [motivation_1](#motivation_1) | Motivation | `Motivation`, `motivation`, `assert_compiles` +8 |
| 2 | [syntax_2](#syntax_2) | Syntax | `Syntax`, `syntax`, `assert_compiles` +11 |
| 3 | [syntax_3](#syntax_3) | Syntax | `Syntax`, `syntax`, `assert_compiles` +11 |
| 4 | [syntax_4](#syntax_4) | Syntax | `Syntax`, `syntax`, `next` +8 |
| 5 | [syntax_5](#syntax_5) | Syntax | `Syntax`, `syntax`, `next` +5 |
| 6 | [fetch_data](#fetch_data) | Effect System Integration | `fetch`, `fetch_data`, `data` +8 |
| 7 | [good_async](#good_async) | Effect System Integration | `GoodAsync`, `Async`, `Good` +7 |
| 8 | [wrapper](#wrapper) | Effect System Integration | `Wrapper`, `wrapper`, `ERROR` +3 |
| 9 | [interaction_with_existing_constructs_9](#interaction_with_existing_constructs_9) | Interaction with Existing Constructs | `existing`, `Existing`, `InteractionWithExistingConstructs` +15 |
| 10 | [load_config](#load_config) | Interaction with Existing Constructs | `load`, `LoadConfig`, `Config` +9 |
| 11 | [interaction_with_existing_constructs_11](#interaction_with_existing_constructs_11) | Interaction with Existing Constructs | `existing`, `Existing`, `InteractionWithExistingConstructs` +18 |
| 12 | [interaction_with_existing_constructs_12](#interaction_with_existing_constructs_12) | Interaction with Existing Constructs | `existing`, `Existing`, `InteractionWithExistingConstructs` +17 |
| 13 | [get_user](#get_user) | Examples | `user`, `User`, `get` +7 |
| 14 | [wait_for_ready](#wait_for_ready) | Examples | `Ready`, `Wait`, `wait_for_ready` +13 |
| 15 | [fetch_and_merge](#fetch_and_merge) | Examples | `fetch`, `merge`, `fetch_and_merge` +13 |
| 16 | [smart_fetch](#smart_fetch) | Examples | `fetch`, `SmartFetch`, `smart_fetch` +10 |
| 17 | [process_stream](#process_stream) | Examples | `process`, `stream`, `Stream` +12 |
| 18 | [examples_18](#examples_18) | Examples | `Examples`, `examples`, `assert_compiles` +11 |
| 19 | [compound_suspending_assignment_19](#compound_suspending_assignment_19) | Compound Suspending Assignment | `compound`, `Compound`, `Suspending` +12 |
| 20 | [chained_suspending_conditions_20](#chained_suspending_conditions_20) | Chained Suspending Conditions | `Suspending`, `ChainedSuspendingConditions`, `suspending` +17 |
| 21 | [implementation_notes_21](#implementation_notes_21) | Implementation Notes | `implementation`, `ImplementationNotes`, `Notes` +7 |
| 22 | [implementation_notes_22](#implementation_notes_22) | Implementation Notes | `implementation`, `ImplementationNotes`, `Notes` +7 |
| 23 | [migration_guide_23](#migration_guide_23) | Migration Guide | `migration_guide`, `MigrationGuide`, `Migration` +8 |
| 24 | [migration_guide_24](#migration_guide_24) | Migration Guide | `migration_guide`, `MigrationGuide`, `Migration` +11 |

---

### Test 1: Motivation {#motivation_1}

**Test name:** `motivation_1`

**Linked Symbols:**
- `Motivation`
- `motivation`
- `assert_compiles`
- `Ready`
- `Hard`
- `Does`
- `fetch_status`
- `Problem`
- `is_up`
- `retry`
- ... and 1 more

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

### Test 2: Syntax {#syntax_2}

**Test name:** `syntax_2`

**Linked Symbols:**
- `Syntax`
- `syntax`
- `assert_compiles`
- `Mutable`
- `Type`
- `Discard`
- `User`
- `load_data`
- `get_initial_count`
- `result`
- ... and 4 more

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

### Test 3: Syntax {#syntax_3}

**Test name:** `syntax_3`

**Linked Symbols:**
- `Syntax`
- `syntax`
- `assert_compiles`
- `fail`
- `Suspending`
- `is_server_ready`
- `Multiple`
- `has_permission`
- `use_fallback`
- `start_processing`
- ... and 4 more

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

### Test 4: Syntax {#syntax_4}

**Test name:** `syntax_4`

**Linked Symbols:**
- `Syntax`
- `syntax`
- `next`
- `assert_compiles`
- `Waiting`
- `process`
- `Poll`
- `is_ready`
- `sleep`
- `Process`
- ... and 1 more

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

### Test 5: Syntax {#syntax_5}

**Test name:** `syntax_5`

**Linked Symbols:**
- `Syntax`
- `syntax`
- `next`
- `assert_compiles`
- `Async`
- `process`
- `Equivalent`
- `async_stream`

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

### Test 6: Effect System Integration {#fetch_data}

**Test name:** `fetch_data`

**Linked Symbols:**
- `fetch`
- `fetch_data`
- `data`
- `Data`
- `Fetch`
- `FetchData`
- `Explicitly`
- `process`
- `get`
- `Result`
- ... and 1 more

**Code:**

```simple
fn fetch_data() -> Data:
    let response ~= http.get(url)
    return parse(response)

# Explicitly async
async fn process() -> Result:
    ...
```

### Test 7: Effect System Integration {#good_async}

**Test name:** `good_async`

**Linked Symbols:**
- `GoodAsync`
- `Async`
- `Good`
- `good_async`
- `good`
- `async`
- `fetch`
- `Increment`
- `ERROR`
- `Counter`

**Code:**

```simple
fn good_async():
    let x ~= fetch()    # OK: fn allows suspension

actor Counter:
    on Increment(n: i64) async:
        let x ~= fetch()    # ERROR: actor handlers are run-to-completion
```

### Test 8: Effect System Integration {#wrapper}

**Test name:** `wrapper`

**Linked Symbols:**
- `Wrapper`
- `wrapper`
- `ERROR`
- `caller`
- `Data`
- `inner_fetch`

**Code:**

```simple
fn wrapper() -> Data:
    let x ~= inner_fetch()   # wrapper is now suspending
    return x

sync fn caller():
    let d = wrapper()        # ERROR: calling suspending fn from sync
```

### Test 9: Interaction with Existing Constructs {#interaction_with_existing_constructs_9}

**Test name:** `interaction_with_existing_constructs_9`

**Linked Symbols:**
- `existing`
- `Existing`
- `InteractionWithExistingConstructs`
- `with`
- `interaction`
- `Interaction`
- `constructs`
- `Constructs`
- `With`
- `interaction_with_existing_constructs`
- ... and 8 more

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

### Test 10: Interaction with Existing Constructs {#load_config}

**Test name:** `load_config`

**Linked Symbols:**
- `load`
- `LoadConfig`
- `Config`
- `config`
- `Load`
- `load_config`
- `Equivalent`
- `Result`
- `parse`
- `Suspend`
- ... and 2 more

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

### Test 11: Interaction with Existing Constructs {#interaction_with_existing_constructs_11}

**Test name:** `interaction_with_existing_constructs_11`

**Linked Symbols:**
- `existing`
- `Existing`
- `InteractionWithExistingConstructs`
- `with`
- `interaction`
- `Interaction`
- `constructs`
- `Constructs`
- `With`
- `interaction_with_existing_constructs`
- ... and 11 more

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

### Test 12: Interaction with Existing Constructs {#interaction_with_existing_constructs_12}

**Test name:** `interaction_with_existing_constructs_12`

**Linked Symbols:**
- `existing`
- `Existing`
- `InteractionWithExistingConstructs`
- `with`
- `interaction`
- `Interaction`
- `constructs`
- `Constructs`
- `With`
- `interaction_with_existing_constructs`
- ... and 10 more

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

### Test 13: Examples {#get_user}

**Test name:** `get_user`

**Linked Symbols:**
- `user`
- `User`
- `get`
- `Get`
- `GetUser`
- `get_user`
- `HttpError`
- `UserId`
- `json`
- `Result`

**Code:**

```simple
fn get_user(id: UserId) -> Result[User, HttpError]:
    let response ~= http.get("/users/{id}")?
    let user: User ~= response.json()?
    return Ok(user)
```

### Test 14: Examples {#wait_for_ready}

**Test name:** `wait_for_ready`

**Linked Symbols:**
- `Ready`
- `Wait`
- `wait_for_ready`
- `WaitForReady`
- `ready`
- `for`
- `For`
- `wait`
- `Timed`
- `now`
- ... and 6 more

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

### Test 15: Examples {#fetch_and_merge}

**Test name:** `fetch_and_merge`

**Linked Symbols:**
- `fetch`
- `merge`
- `fetch_and_merge`
- `Fetch`
- `and`
- `Merge`
- `FetchAndMerge`
- `And`
- `User`
- `all`
- ... and 6 more

**Code:**

```simple
fn fetch_and_merge(ids: [UserId]) -> [User]:
    # Start all fetches in parallel
    let futures = ids.map(\id: fetch_user(id))

    # Wait for all (suspends once)
    let users ~= Future.all(futures)

    return users
```

### Test 16: Examples {#smart_fetch}

**Test name:** `smart_fetch`

**Linked Symbols:**
- `fetch`
- `SmartFetch`
- `smart_fetch`
- `smart`
- `Fetch`
- `Smart`
- `set`
- `Suspending`
- `User`
- `get`
- ... and 3 more

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

### Test 17: Examples {#process_stream}

**Test name:** `process_stream`

**Linked Symbols:**
- `process`
- `stream`
- `Stream`
- `Process`
- `process_stream`
- `ProcessStream`
- `record`
- `Close`
- `new`
- `Data`
- ... and 5 more

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

### Test 18: Examples {#examples_18}

**Test name:** `examples_18`

**Linked Symbols:**
- `Examples`
- `examples`
- `assert_compiles`
- `Query`
- `fetch_remote`
- `Key`
- `task`
- `Value`
- `DataService`
- `Actors`
- ... and 4 more

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

### Test 19: Compound Suspending Assignment {#compound_suspending_assignment_19}

**Test name:** `compound_suspending_assignment_19`

**Linked Symbols:**
- `compound`
- `Compound`
- `Suspending`
- `CompoundSuspendingAssignment`
- `suspending`
- `assignment`
- `Assignment`
- `compound_suspending_assignment`
- `assert_compiles`
- `get_decrement`
- ... and 5 more

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

### Test 20: Chained Suspending Conditions {#chained_suspending_conditions_20}

**Test name:** `chained_suspending_conditions_20`

**Linked Symbols:**
- `Suspending`
- `ChainedSuspendingConditions`
- `suspending`
- `Conditions`
- `conditions`
- `chained_suspending_conditions`
- `Chained`
- `chained`
- `is_online`
- `assert_compiles`
- ... and 10 more

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

### Test 21: Implementation Notes {#implementation_notes_21}

**Test name:** `implementation_notes_21`

**Linked Symbols:**
- `implementation`
- `ImplementationNotes`
- `Notes`
- `Implementation`
- `notes`
- `implementation_notes`
- `assert_compiles`
- `Source`
- `Future`
- `Desugared`

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

### Test 22: Implementation Notes {#implementation_notes_22}

**Test name:** `implementation_notes_22`

**Linked Symbols:**
- `implementation`
- `ImplementationNotes`
- `Notes`
- `Implementation`
- `notes`
- `implementation_notes`
- `assert_compiles`
- `Source`
- `Future`
- `Desugared`

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

### Test 23: Migration Guide {#migration_guide_23}

**Test name:** `migration_guide_23`

**Linked Symbols:**
- `migration_guide`
- `MigrationGuide`
- `Migration`
- `guide`
- `migration`
- `Guide`
- `assert_compiles`
- `fetch`
- `Before`
- `is_ready`
- ... and 1 more

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

### Test 24: Migration Guide {#migration_guide_24}

**Test name:** `migration_guide_24`

**Linked Symbols:**
- `migration_guide`
- `MigrationGuide`
- `Migration`
- `guide`
- `migration`
- `Guide`
- `assert_compiles`
- `fetch`
- `Explicitly`
- `Before`
- ... and 4 more

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

## Source Code

**View full specification:** [suspension_operator_spec.spl](../../tests/specs/suspension_operator_spec.spl)

---

*This file was auto-generated from the executable specification.*
*Source: `tests/specs/suspension_operator_spec.spl`*
