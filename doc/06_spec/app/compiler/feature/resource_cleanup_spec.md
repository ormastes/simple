# Resource Cleanup Framework

**Feature ID:** #RES-001 | **Category:** Infrastructure | **Status:** In Progress

_Source: `test/feature/usage/resource_cleanup_spec.spl`_

---

## Overview

Tests the unified resource cleanup framework including the Resource trait
(close, is_open, resource_name), ResourceRegistry for leak detection with
unique IDs and leak reporting, LeakTracked mixin for automatic registration,
and defer/with statements for scope-based cleanup. Some tests are skipped
in interpreter mode as defer and with are compiler-only features.

## Syntax

```simple
val res = MockResource__open("test")
defer mockresource_close(res)
with open_resource("file.txt") as f:
    f.read()
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 15 |

## Test Structure

### Feature #2300: Resource Trait

#### Resource trait interface

- ✅ close() releases the resource
- ✅ close() is idempotent
- ✅ is_open() returns correct state
- ✅ resource_name() provides descriptive name
### Feature #2301: ResourceRegistry

#### Resource registration

- ✅ registers resources with unique IDs
- ✅ unregisters resources
#### Leak detection

- ✅ check_leaks() returns unclosed resources
- ✅ leak_report() generates human-readable output
- ✅ clear() removes all entries
### Feature #2302: LeakTracked Mixin

#### Automatic tracking

- ✅ auto-registers on _start_tracking()
- ✅ auto-unregisters on _stop_tracking()
- ✅ is_tracked() returns correct state
- ✅ tracking_id() returns Some while tracked
### Feature #2303: defer Statement

#### Basic defer behavior

#### Multiple defers (LIFO order)

#### defer with resources

### Feature #2304: with Statement

#### Basic with statement

#### Usage examples

- ✅ demonstrates defer pattern
- ✅ demonstrates leak detection in tests

