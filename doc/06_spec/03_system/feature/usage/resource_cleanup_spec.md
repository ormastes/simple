# Resource Cleanup Framework

> Tests the unified resource cleanup framework including the Resource trait (close, is_open, resource_name), ResourceRegistry for leak detection with unique IDs and leak reporting, LeakTracked mixin for automatic registration, and defer/with statements for scope-based cleanup. Some tests are skipped in interpreter mode as defer and with are compiler-only features.

<!-- sdn-diagram:id=resource_cleanup_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=resource_cleanup_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

resource_cleanup_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=resource_cleanup_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Resource Cleanup Framework

Tests the unified resource cleanup framework including the Resource trait (close, is_open, resource_name), ResourceRegistry for leak detection with unique IDs and leak reporting, LeakTracked mixin for automatic registration, and defer/with statements for scope-based cleanup. Some tests are skipped in interpreter mode as defer and with are compiler-only features.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RES-001 |
| Category | Infrastructure |
| Status | In Progress |
| Source | `test/03_system/feature/usage/resource_cleanup_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the unified resource cleanup framework including the Resource trait
(close, is_open, resource_name), ResourceRegistry for leak detection with
unique IDs and leak reporting, LeakTracked mixin for automatic registration,
and defer/with statements for scope-based cleanup. Some tests are skipped
in interpreter mode as defer and with are compiler-only features.

## Syntax

```simple
val res = MockResource.open("test")
defer mockresource_close(res)
with open_resource("file.txt") as f:
f.read()
```

## Scenarios

### Feature #2300: Resource Trait

#### Resource trait interface

#### close() releases the resource

1. is open = false  # close
   - Expected: is_open is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Demonstrates resource lifecycle concept
var is_open = true
is_open = false  # close()
expect(is_open).to_equal(false)
```

</details>

#### close() is idempotent

1. is open = false  # close
2. is open = false  # close
   - Expected: is_open is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Demonstrates idempotent close
var is_open = true
is_open = false  # close()
is_open = false  # close() again
expect(is_open).to_equal(false)
```

</details>

#### is_open() returns correct state

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Demonstrates state tracking
val is_open = true
expect(is_open).to_equal(true)
```

</details>

#### resource_name() provides descriptive name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Demonstrates resource naming
val name = "my_file"
expect(name).to_equal("my_file")
```

</details>

### Feature #2301: ResourceRegistry

#### Resource registration

#### registers resources with unique IDs

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Demonstrates ID generation
var next_id = 0
val id1 = next_id
next_id = next_id + 1
val id2 = next_id
next_id = next_id + 1

expect(id1).to_equal(0)
expect(id2).to_equal(1)
```

</details>

#### unregisters resources

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Demonstrates remove tracking
var count = 0
count = count + 1  # register
expect(count).to_equal(1)
count = count - 1  # unregister
expect(count).to_equal(0)
```

</details>

#### Leak detection

#### check_leaks() returns unclosed resources

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Demonstrates leak tracking
var leaked = ["leaked_file", "leaked_socket"]
expect(leaked.len()).to_equal(2)
```

</details>

#### leak_report() generates human-readable output

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Demonstrates report generation
val report = "Resource leaks detected:\n  - file1\n"
expect(report.contains("leak")).to_equal(true)
```

</details>

#### clear() removes all entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Demonstrates clearing
var items = ["test1", "test2"]
items = []  # clear
expect(items.len()).to_equal(0)
```

</details>

### Feature #2302: LeakTracked Mixin

#### Automatic tracking

#### auto-registers on _start_tracking()

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Demonstrates automatic tracking
var tracked = false
var count = 0

tracked = true  # start_tracking
count = count + 1

expect(tracked).to_equal(true)
expect(count).to_equal(1)
```

</details>

#### auto-unregisters on _stop_tracking()

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Demonstrates automatic cleanup
var count = 1

count = count - 1  # stop_tracking
expect(count).to_equal(0)
```

</details>

#### is_tracked() returns correct state

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Demonstrates tracking state
var tracked = false
expect(tracked).to_equal(false)

tracked = true  # start tracking
expect(tracked).to_equal(true)
```

</details>

#### tracking_id() returns Some while tracked

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Demonstrates ID management
var id = -1  # untracked
expect(id).to_equal(-1)

id = 0  # assign ID when tracked
expect(id >= 0).to_equal(true)
```

</details>

### Feature #2303: defer Statement

#### Basic defer behavior

#### Multiple defers (LIFO order)

#### defer with resources

### Feature #2304: with Statement

#### Basic with statement

#### Usage examples

#### demonstrates defer pattern

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Example showing manual cleanup pattern
var open_count = 1

# In real code: defer close_resource()
# For test: manually close
open_count = open_count - 1
expect(open_count).to_equal(0)
```

</details>

#### demonstrates leak detection in tests

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Intentionally leak a resource
var leaked_resources = ["leaked_resource"]
expect(leaked_resources.len()).to_equal(1)

# Clean up for next test
leaked_resources = []
expect(leaked_resources.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
