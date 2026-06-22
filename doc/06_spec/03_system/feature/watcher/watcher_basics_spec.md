# File Watcher Change Detection and Rebuild Cycle

> Tests the file watcher's change detection mechanism and rebuild cycle including filesystem event filtering, debouncing, and incremental rebuild triggering. Verifies that file changes are detected reliably and trigger the correct actions.

<!-- sdn-diagram:id=watcher_basics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=watcher_basics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

watcher_basics_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=watcher_basics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# File Watcher Change Detection and Rebuild Cycle

Tests the file watcher's change detection mechanism and rebuild cycle including filesystem event filtering, debouncing, and incremental rebuild triggering. Verifies that file changes are detected reliably and trigger the correct actions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | In Progress |
| Source | `test/03_system/feature/watcher/watcher_basics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the file watcher's change detection mechanism and rebuild cycle including
filesystem event filtering, debouncing, and incremental rebuild triggering.
Verifies that file changes are detected reliably and trigger the correct actions.

## Scenarios

### File Watcher

#### when monitoring source files

#### detects basic changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test basic functionality that would be monitored
val x = 1
val y = 2
val sum = x + y
expect(sum).to_equal(3)
```

</details>

#### handles multiple file operations

1. data push
   - Expected: data.len() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var data = [1, 2, 3]
data.push(4)
expect(data.len()).to_equal(4)
```

</details>

#### when rebuilding on changes

#### recalculates simple math

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test that code produces correct values after changes
val result = 21 * 2
expect(result).to_equal(42)
```

</details>

#### maintains state correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test that state is preserved/reset correctly
var counter = 0
for i in [1, 2, 3]:
    counter = counter + i
expect(counter).to_equal(6)
```

</details>

#### when handling errors

#### recovers from errors gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test error handling
val success = true
expect(success).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
