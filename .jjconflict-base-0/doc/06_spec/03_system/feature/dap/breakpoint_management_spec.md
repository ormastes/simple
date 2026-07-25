# DAP Breakpoint Management

> Tests the Debug Adapter Protocol breakpoint management including setting, removing, and hit-count breakpoints. Verifies that breakpoints are correctly tracked across source locations and that conditional breakpoints evaluate their expressions.

<!-- sdn-diagram:id=breakpoint_management_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=breakpoint_management_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

breakpoint_management_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=breakpoint_management_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DAP Breakpoint Management

Tests the Debug Adapter Protocol breakpoint management including setting, removing, and hit-count breakpoints. Verifies that breakpoints are correctly tracked across source locations and that conditional breakpoints evaluate their expressions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Developer Tools |
| Status | In Progress |
| Source | `test/03_system/feature/dap/breakpoint_management_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the Debug Adapter Protocol breakpoint management including setting, removing,
and hit-count breakpoints. Verifies that breakpoints are correctly tracked across
source locations and that conditional breakpoints evaluate their expressions.

## Scenarios

### Breakpoint Management

### Adding breakpoints

#### adds a single breakpoint

1. debug set active
2. debug add breakpoint
   - Expected: has_bp is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_add_breakpoint("test.spl", 10, 1)

val has_bp = debug_has_breakpoint("test.spl", 10)
expect(has_bp).to_equal(true)
```

</details>

#### adds multiple breakpoints in same file

1. debug set active
2. debug add breakpoint
3. debug add breakpoint
4. debug add breakpoint
   - Expected: debug_has_breakpoint("test.spl", 10) is true
   - Expected: debug_has_breakpoint("test.spl", 20) is true
   - Expected: debug_has_breakpoint("test.spl", 30) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_add_breakpoint("test.spl", 10, 1)
debug_add_breakpoint("test.spl", 20, 2)
debug_add_breakpoint("test.spl", 30, 3)

expect(debug_has_breakpoint("test.spl", 10)).to_equal(true)
expect(debug_has_breakpoint("test.spl", 20)).to_equal(true)
expect(debug_has_breakpoint("test.spl", 30)).to_equal(true)
```

</details>

#### adds breakpoints in different files

1. debug set active
2. debug add breakpoint
3. debug add breakpoint
   - Expected: debug_has_breakpoint("file1.spl", 10) is true
   - Expected: debug_has_breakpoint("file2.spl", 15) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_add_breakpoint("file1.spl", 10, 1)
debug_add_breakpoint("file2.spl", 15, 2)

expect(debug_has_breakpoint("file1.spl", 10)).to_equal(true)
expect(debug_has_breakpoint("file2.spl", 15)).to_equal(true)
```

</details>

#### allows duplicate breakpoints with different IDs

1. debug set active
2. debug add breakpoint
3. debug add breakpoint
   - Expected: has_bp is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_add_breakpoint("test.spl", 10, 1)
debug_add_breakpoint("test.spl", 10, 2)  # Same location, different ID

val has_bp = debug_has_breakpoint("test.spl", 10)
expect(has_bp).to_equal(true)
```

</details>

### Removing breakpoints

#### removes a breakpoint

1. debug set active
2. debug add breakpoint
   - Expected: debug_has_breakpoint("test.spl", 10) is true
3. debug remove breakpoint
   - Expected: debug_has_breakpoint("test.spl", 10) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_add_breakpoint("test.spl", 10, 1)
expect(debug_has_breakpoint("test.spl", 10)).to_equal(true)

debug_remove_breakpoint("test.spl", 10)
expect(debug_has_breakpoint("test.spl", 10)).to_equal(false)
```

</details>

#### removes specific breakpoint from multiple

1. debug set active
2. debug add breakpoint
3. debug add breakpoint
4. debug add breakpoint
5. debug remove breakpoint
   - Expected: debug_has_breakpoint("test.spl", 10) is true
   - Expected: debug_has_breakpoint("test.spl", 20) is false
   - Expected: debug_has_breakpoint("test.spl", 30) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_add_breakpoint("test.spl", 10, 1)
debug_add_breakpoint("test.spl", 20, 2)
debug_add_breakpoint("test.spl", 30, 3)

debug_remove_breakpoint("test.spl", 20)

expect(debug_has_breakpoint("test.spl", 10)).to_equal(true)
expect(debug_has_breakpoint("test.spl", 20)).to_equal(false)
expect(debug_has_breakpoint("test.spl", 30)).to_equal(true)
```

</details>

#### handles removing non-existent breakpoint

1. debug set active
2. debug remove breakpoint
   - Expected: debug_has_breakpoint("test.spl", 999) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
# Should not crash
debug_remove_breakpoint("test.spl", 999)
expect(debug_has_breakpoint("test.spl", 999)).to_equal(false)
```

</details>

### Checking breakpoint existence

#### returns false for non-existent breakpoint

1. debug set active
   - Expected: has_bp is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
val has_bp = debug_has_breakpoint("nonexistent.spl", 100)
expect(has_bp).to_equal(false)
```

</details>

#### checks breakpoint in correct file only

1. debug set active
2. debug add breakpoint
   - Expected: debug_has_breakpoint("file1.spl", 10) is true
   - Expected: debug_has_breakpoint("file2.spl", 10) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_add_breakpoint("file1.spl", 10, 1)

expect(debug_has_breakpoint("file1.spl", 10)).to_equal(true)
expect(debug_has_breakpoint("file2.spl", 10)).to_equal(false)
```

</details>

#### checks breakpoint at correct line only

1. debug set active
2. debug add breakpoint
   - Expected: debug_has_breakpoint("test.spl", 10) is true
   - Expected: debug_has_breakpoint("test.spl", 9) is false
   - Expected: debug_has_breakpoint("test.spl", 11) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_add_breakpoint("test.spl", 10, 1)

expect(debug_has_breakpoint("test.spl", 10)).to_equal(true)
expect(debug_has_breakpoint("test.spl", 9)).to_equal(false)
expect(debug_has_breakpoint("test.spl", 11)).to_equal(false)
```

</details>

### Breakpoint hit detection

#### should break when at breakpoint location

1. debug set active
2. debug add breakpoint
3. debug set current location
   - Expected: should_break is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_add_breakpoint("test.spl", 42, 1)
debug_set_current_location("test.spl", 42, 0)

val should_break = debug_should_break()
expect(should_break).to_equal(true)
```

</details>

#### should not break when not at breakpoint

1. debug set active
2. debug add breakpoint
3. debug set current location
   - Expected: should_break is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_add_breakpoint("test.spl", 42, 1)
debug_set_current_location("test.spl", 43, 0)

val should_break = debug_should_break()
expect(should_break).to_equal(false)
```

</details>

#### should not break when debug inactive

1. debug set active
2. debug add breakpoint
3. debug set current location
   - Expected: should_break is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(false)
debug_add_breakpoint("test.spl", 42, 1)
debug_set_current_location("test.spl", 42, 0)

val should_break = debug_should_break()
expect(should_break).to_equal(false)
```

</details>

### Edge cases

#### handles line number 0

1. debug set active
2. debug add breakpoint
   - Expected: debug_has_breakpoint("test.spl", 0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_add_breakpoint("test.spl", 0, 1)
expect(debug_has_breakpoint("test.spl", 0)).to_equal(true)
```

</details>

#### handles large line numbers

1. debug set active
2. debug add breakpoint
   - Expected: debug_has_breakpoint("test.spl", 999999) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_add_breakpoint("test.spl", 999999, 1)
expect(debug_has_breakpoint("test.spl", 999999)).to_equal(true)
```

</details>

#### handles empty file path

1. debug set active
2. debug add breakpoint
   - Expected: debug_has_breakpoint("", 10) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_add_breakpoint("", 10, 1)
expect(debug_has_breakpoint("", 10)).to_equal(true)
```

</details>

#### handles special characters in file path

1. debug set active
2. debug add breakpoint
   - Expected: debug_has_breakpoint("path/to/my-file_v2.spl", 10) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_add_breakpoint("path/to/my-file_v2.spl", 10, 1)
expect(debug_has_breakpoint("path/to/my-file_v2.spl", 10)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
