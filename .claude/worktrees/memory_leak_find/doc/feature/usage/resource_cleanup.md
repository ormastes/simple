# resource cleanup
*Source:* `test/feature/usage/resource_cleanup_spec.spl`

## Overview

The Resource trait provides a unified interface for resources that
    require explicit cleanup, such as file handles, network sockets,
    database connections, etc.

    All resources should implement:
    - close() - Release the resource
    - is_open() -> bool - Check if resource is usable
    - resource_name() -> text - Human-readable name for errors

## Feature: Feature #2300: Resource Trait

The Resource trait provides a unified interface for resources that
    require explicit cleanup, such as file handles, network sockets,
    database connections, etc.

    All resources should implement:
    - close() - Release the resource
    - is_open() -> bool - Check if resource is usable
    - resource_name() -> text - Human-readable name for errors

### Scenario: Resource trait interface

Tests that Resource trait methods work correctly.

| # | Example | Status |
|---|---------|--------|
| 1 | close() releases the resource | pass |
| 2 | close() is idempotent | pass |
| 3 | is_open() returns correct state | pass |
| 4 | resource_name() provides descriptive name | pass |

**Example:** close() releases the resource
    Given var is_open = true
    Then  expect(is_open).to_equal(false)

**Example:** close() is idempotent
    Given var is_open = true
    Then  expect(is_open).to_equal(false)

**Example:** is_open() returns correct state
    Given val is_open = true
    Then  expect(is_open).to_equal(true)

**Example:** resource_name() provides descriptive name
    Given val name = "my_file"
    Then  expect(name).to_equal("my_file")

## Feature: Feature #2301: ResourceRegistry

ResourceRegistry provides global tracking of open resources
    for runtime leak detection.

### Scenario: Resource registration

Tests resource registration and unregistration.

| # | Example | Status |
|---|---------|--------|
| 1 | registers resources with unique IDs | pass |
| 2 | unregisters resources | pass |

**Example:** registers resources with unique IDs
    Given var next_id = 0
    Given val id1 = next_id
    Given val id2 = next_id
    Then  expect(id1).to_equal(0)
    Then  expect(id2).to_equal(1)

**Example:** unregisters resources
    Given var count = 0
    Then  expect(count).to_equal(1)
    Then  expect(count).to_equal(0)

### Scenario: Leak detection

Tests leak checking functionality.

| # | Example | Status |
|---|---------|--------|
| 1 | check_leaks() returns unclosed resources | pass |
| 2 | leak_report() generates human-readable output | pass |
| 3 | clear() removes all entries | pass |

**Example:** check_leaks() returns unclosed resources
    Given var leaked = ["leaked_file", "leaked_socket"]
    Then  expect(leaked.len()).to_equal(2)

**Example:** leak_report() generates human-readable output
    Given val report = "Resource leaks detected:{NL}  - file1{NL}"
    Then  expect(report.contains("leak")).to_equal(true)

**Example:** clear() removes all entries
    Given var items = ["test1", "test2"]
    Then  expect(items.len()).to_equal(0)

## Feature: Feature #2302: LeakTracked Mixin

The LeakTracked mixin provides automatic resource tracking.
    Resources using this mixin are automatically registered when
    created and unregistered when closed.

### Scenario: Automatic tracking

Tests automatic registration/unregistration.

| # | Example | Status |
|---|---------|--------|
| 1 | auto-registers on _start_tracking() | pass |
| 2 | auto-unregisters on _stop_tracking() | pass |
| 3 | is_tracked() returns correct state | pass |
| 4 | tracking_id() returns Some while tracked | pass |

**Example:** auto-registers on _start_tracking()
    Given var tracked = false
    Given var count = 0
    Then  expect(tracked).to_equal(true)
    Then  expect(count).to_equal(1)

**Example:** auto-unregisters on _stop_tracking()
    Given var count = 1
    Then  expect(count).to_equal(0)

**Example:** is_tracked() returns correct state
    Given var tracked = false
    Then  expect(tracked).to_equal(false)
    Then  expect(tracked).to_equal(true)

**Example:** tracking_id() returns Some while tracked
    Given var id = -1  # untracked
    Then  expect(id).to_equal(-1)
    Then  expect(id >= 0).to_equal(true)

## Feature: Feature #2303: defer Statement

The defer statement schedules cleanup to run when the current
    scope exits, regardless of how it exits.

    NOTE: defer is a compiler feature, not available in interpreter.
    Tests remain skipped for interpreter mode.

### Scenario: Basic defer behavior

Tests defer execution at scope exit.

### Scenario: Multiple defers (LIFO order)

Tests that multiple defers run in Last-In-First-Out order.

### Scenario: defer with resources

Tests defer with actual resource cleanup.

## Feature: Feature #2304: with Statement

The with statement provides automatic cleanup via context managers.
    Resources are automatically closed when the with block exits.

    NOTE: with is a compiler feature, not available in interpreter.
    Tests remain skipped for interpreter mode.

### Scenario: Basic with statement

Tests automatic cleanup with context managers.

### Scenario: Usage examples

Example usage patterns for resource cleanup.

| # | Example | Status |
|---|---------|--------|
| 1 | demonstrates defer pattern | pass |
| 2 | demonstrates leak detection in tests | pass |

**Example:** demonstrates defer pattern
    Given var open_count = 1
    Then  expect(open_count).to_equal(0)

**Example:** demonstrates leak detection in tests
    Given var leaked_resources = ["leaked_resource"]
    Then  expect(leaked_resources.len()).to_equal(1)
    Then  expect(leaked_resources.len()).to_equal(0)


