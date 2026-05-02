# Context Managers Specification
*Source:* `test/feature/usage/context_managers_spec.spl`
**Feature IDs:** #CONTEXT-MANAGER  |  **Category:** Language  |  **Status:** Implemented

## Overview



Context managers provide a way to safely acquire and release resources using
the `with` statement. They implement the resource protocol with `__enter__()` and
`__exit__()` methods, ensuring cleanup code runs reliably even when exceptions occur.

## Syntax

```simple
with resource as alias:
    # code using alias
    # __exit__ is called after this block
```

## Key Behaviors

- `__enter__()` is called on entry, its return value is bound to alias
- `__exit__()` is always called, even if an exception occurs
- Alias binding can coexist with parser special handling (e.g., cast expressions)
- Clean separation between resource acquisition and usage
- Exception safety: cleanup always happens

## Feature: Context Managers

Verifies that context managers provide safe resource acquisition and
    cleanup through the `with` statement. Tests cover basic entry/exit
    semantics, alias binding, and integration with other language features.

### Scenario: basic context manager protocol

| # | Example | Status |
|---|---------|--------|
| 1 | calls __enter__ and binds result to alias | pass |
| 2 | calls __exit__ after block completes | pass |

**Example:** calls __enter__ and binds result to alias
    Given var captured = 0
    Then  expect captured == 15

**Example:** calls __exit__ after block completes
    Given val resource = Resource(value: 42)
    Then  expect resource.exited == true

### Scenario: alias binding and reuse

| # | Example | Status |
|---|---------|--------|
| 1 | reuses identifier when parser sees cast-style syntax | pass |
| 2 | properly binds alias in nested contexts | pass |

**Example:** reuses identifier when parser sees cast-style syntax
    Given var result = 0
    Given val inner = alias
    Then  expect result == 3

**Example:** properly binds alias in nested contexts
    Given var results = []
    Then  expect results == [10, 6, 10]

### Scenario: resource cleanup

| # | Example | Status |
|---|---------|--------|
| 1 | runs cleanup code after block | pass |
| 2 | runs cleanup even after multiple operations | pass |

**Example:** runs cleanup code after block
    Given val resource = Resource()
    Then  expect resource.cleanup_count == 1

**Example:** runs cleanup even after multiple operations
    Given val resource = Resource()
    Then  expect resource.operations == 3
    Then  expect resource.exit_called == true

### Scenario: using acquired values

| # | Example | Status |
|---|---------|--------|
| 1 | can use alias from __enter__ return value | pass |
| 2 | can call methods on alias | pass |

**Example:** can use alias from __enter__ return value
    Given var loaded = ""
    Then  expect loaded == "loaded content"

**Example:** can call methods on alias
    Given var result = 0
    Then  expect result == 42

### Scenario: exception handling

| # | Example | Status |
|---|---------|--------|
| 1 | passes exception info to __exit__ | pass |
| 2 | always calls __exit__ for resource cleanup | pass |

**Example:** passes exception info to __exit__
    Given val resource = Resource()
    Then  expect resource.exception_passed == false

**Example:** always calls __exit__ for resource cleanup
    Given val resource = Resource()
    Given val result = 0
    Given val temp = value + 1
    Then  expect resource.exit_was_called == true

### Scenario: multiple resources

| # | Example | Status |
|---|---------|--------|
| 1 | can nest multiple context managers | pass |
| 2 | cleans up in reverse order | pass |

**Example:** can nest multiple context managers
    Given val r1 = Resource(id: 1)
    Given val r2 = Resource(id: 2)
    Given var results = []
    Then  expect results == [1, 2]
    Then  expect r1.exited == true
    Then  expect r2.exited == true

### Scenario: practical patterns

| # | Example | Status |
|---|---------|--------|
| 1 | implements file-like resource pattern | pass |
| 2 | ensures state is restored on exit | pass |

**Example:** implements file-like resource pattern
    Given val file = File(filename: "data.txt")
    Given var content = ""
    Then  expect file.is_open == true
    Then  expect file.is_open == false
    Then  expect content == "file content"

**Example:** ensures state is restored on exit
    Given val manager = StateManager()
    Given var temp = ""
    Then  expect manager.state == "active"
    Then  expect manager.state == "cleaned"


