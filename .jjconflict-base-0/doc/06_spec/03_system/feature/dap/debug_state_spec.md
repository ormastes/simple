# DAP Debug State Management

> Tests the Debug Adapter Protocol state machine including launch, attach, running, stopped, and terminated states. Verifies correct state transitions and that state queries return accurate information about the debuggee.

<!-- sdn-diagram:id=debug_state_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=debug_state_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

debug_state_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=debug_state_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DAP Debug State Management

Tests the Debug Adapter Protocol state machine including launch, attach, running, stopped, and terminated states. Verifies correct state transitions and that state queries return accurate information about the debuggee.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Developer Tools |
| Status | In Progress |
| Source | `test/03_system/feature/dap/debug_state_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the Debug Adapter Protocol state machine including launch, attach, running,
stopped, and terminated states. Verifies correct state transitions and that
state queries return accurate information about the debuggee.

## Scenarios

### Debug Activation

#### starts inactive by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Debug should be off by default for performance
val active = debug_is_active()
expect(active).to_equal(false)
```

</details>

#### activates debug mode

1. debug set active
   - Expected: debug_is_active() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
expect(debug_is_active()).to_equal(true)
```

</details>

#### deactivates debug mode

1. debug set active
2. debug set active
   - Expected: debug_is_active() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_active(false)
expect(debug_is_active()).to_equal(false)
```

</details>

#### toggles debug mode

1. debug set active
   - Expected: debug_is_active() is true
2. debug set active
   - Expected: debug_is_active() is false
3. debug set active
   - Expected: debug_is_active() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
expect(debug_is_active()).to_equal(true)

debug_set_active(false)
expect(debug_is_active()).to_equal(false)

debug_set_active(true)
expect(debug_is_active()).to_equal(true)
```

</details>

### Pause and Continue

### Pause operations

#### starts not paused

1. debug set active
   - Expected: paused is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
val paused = debug_is_paused()
expect(paused).to_equal(false)
```

</details>

#### pauses execution

1. debug set active
2. debug pause
   - Expected: debug_is_paused() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_pause()
expect(debug_is_paused()).to_equal(true)
```

</details>

#### can pause multiple times

1. debug set active
2. debug pause
3. debug pause
   - Expected: debug_is_paused() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_pause()
debug_pause()  # Should be idempotent
expect(debug_is_paused()).to_equal(true)
```

</details>

### Continue operations

#### continues from paused state

1. debug set active
2. debug pause
   - Expected: debug_is_paused() is true
3. debug continue
   - Expected: debug_is_paused() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_pause()
expect(debug_is_paused()).to_equal(true)

debug_continue()
expect(debug_is_paused()).to_equal(false)
```

</details>

#### can continue when not paused

1. debug set active
2. debug continue
   - Expected: debug_is_paused() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_continue()  # Should be safe
expect(debug_is_paused()).to_equal(false)
```

</details>

### Pause/continue cycle

#### handles multiple pause/continue cycles

1. debug set active
2. debug pause
   - Expected: debug_is_paused() is true
3. debug continue
   - Expected: debug_is_paused() is false
4. debug pause
   - Expected: debug_is_paused() is true
5. debug continue
   - Expected: debug_is_paused() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)

debug_pause()
expect(debug_is_paused()).to_equal(true)

debug_continue()
expect(debug_is_paused()).to_equal(false)

debug_pause()
expect(debug_is_paused()).to_equal(true)

debug_continue()
expect(debug_is_paused()).to_equal(false)
```

</details>

### Location Tracking

### Setting location

#### sets current file and line

1. debug set active
2. debug set current location
   - Expected: file equals `test.spl`
   - Expected: line equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_current_location("test.spl", 42, 5)

val file = debug_current_file()
val line = debug_current_line()

expect(file).to_equal("test.spl")
expect(line).to_equal(42)
```

</details>

#### updates location multiple times

1. debug set active
2. debug set current location
   - Expected: debug_current_file() equals `file1.spl`
3. debug set current location
   - Expected: debug_current_file() equals `file2.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_current_location("file1.spl", 10, 0)
expect(debug_current_file()).to_equal("file1.spl")

debug_set_current_location("file2.spl", 20, 0)
expect(debug_current_file()).to_equal("file2.spl")
```

</details>

#### tracks location through different files

1. debug set active
2. debug set current location
   - Expected: debug_current_file() equals `main.spl`
   - Expected: debug_current_line() equals `10`
3. debug set current location
   - Expected: debug_current_file() equals `utils.spl`
   - Expected: debug_current_line() equals `55`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)

debug_set_current_location("main.spl", 10, 0)
expect(debug_current_file()).to_equal("main.spl")
expect(debug_current_line()).to_equal(10)

debug_set_current_location("utils.spl", 55, 8)
expect(debug_current_file()).to_equal("utils.spl")
expect(debug_current_line()).to_equal(55)
```

</details>

### Getting location

#### returns current file

1. debug set active
2. debug set current location
   - Expected: file equals `myfile.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_current_location("myfile.spl", 10, 0)

val file = debug_current_file()
expect(file).to_equal("myfile.spl")
```

</details>

#### returns current line

1. debug set active
2. debug set current location
   - Expected: line equals `123`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_current_location("test.spl", 123, 0)

val line = debug_current_line()
expect(line).to_equal(123)
```

</details>

#### tracks line changes in same file

1. debug set active
2. debug set current location
   - Expected: debug_current_line() equals `10`
3. debug set current location
   - Expected: debug_current_line() equals `11`
4. debug set current location
   - Expected: debug_current_line() equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_current_location("test.spl", 10, 0)
expect(debug_current_line()).to_equal(10)

debug_set_current_location("test.spl", 11, 0)
expect(debug_current_line()).to_equal(11)

debug_set_current_location("test.spl", 12, 0)
expect(debug_current_line()).to_equal(12)
```

</details>

### Edge cases

#### handles line 0

1. debug set active
2. debug set current location
   - Expected: debug_current_line() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_current_location("test.spl", 0, 0)
expect(debug_current_line()).to_equal(0)
```

</details>

#### handles large line numbers

1. debug set active
2. debug set current location
   - Expected: debug_current_line() equals `999999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_current_location("test.spl", 999999, 0)
expect(debug_current_line()).to_equal(999999)
```

</details>

#### handles empty file path

1. debug set active
2. debug set current location
   - Expected: file equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_current_location("", 10, 0)
val file = debug_current_file()
expect(file).to_equal("")
```

</details>

#### handles paths with special characters

1. debug set active
2. debug set current location
   - Expected: debug_current_file() equals `path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
val path = "src/app/my-module_v2.spl"
debug_set_current_location(path, 10, 0)
expect(debug_current_file()).to_equal(path)
```

</details>

#### handles absolute paths

1. debug set active
2. debug set current location
   - Expected: debug_current_file() equals `path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
val path = "/home/user/project/src/main.spl"
debug_set_current_location(path, 10, 0)
expect(debug_current_file()).to_equal(path)
```

</details>

#### handles relative paths

1. debug set active
2. debug set current location
   - Expected: debug_current_file() equals `path`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
val path = "./src/main.spl"
debug_set_current_location(path, 10, 0)
expect(debug_current_file()).to_equal(path)
```

</details>

### State Persistence

#### maintains state across operations

1. debug set active
2. debug set current location
3. debug pause
   - Expected: debug_is_active() is true
   - Expected: debug_current_file() equals `test.spl`
   - Expected: debug_current_line() equals `10`
   - Expected: debug_is_paused() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_current_location("test.spl", 10, 0)
debug_pause()

# State should persist
expect(debug_is_active()).to_equal(true)
expect(debug_current_file()).to_equal("test.spl")
expect(debug_current_line()).to_equal(10)
expect(debug_is_paused()).to_equal(true)
```

</details>

#### preserves location when toggling debug

1. debug set active
2. debug set current location
3. debug set active
4. debug set active
   - Expected: file equals `test.spl`
   - Expected: line equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_current_location("test.spl", 42, 0)

debug_set_active(false)
debug_set_active(true)

# Location may or may not persist - implementation dependent
# Just verify no crash
val file = debug_current_file()
val line = debug_current_line()
expect(file).to_equal("test.spl")
expect(line).to_equal(42)
```

</details>

### Performance and Overhead

#### has no overhead when inactive

1. debug set active
2. debug is active
   - Expected: debug_is_active() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(false)

# These operations should be extremely fast when debug off
for i in 0..1000:
    debug_is_active()  # Should return immediately

expect(debug_is_active()).to_equal(false)
```

</details>

#### handles high frequency location updates

1. debug set active
2. debug set current location
   - Expected: line >= 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)

# Simulate expression evaluation on every line
for i in 0..1000:
    debug_set_current_location("test.spl", i, 0)

val line = debug_current_line()
expect(line >= 0).to_equal(true)
```

</details>

### Integration Scenarios

#### tracks location while stepping

1. debug set active
2. debug set step mode
3. debug set current location
   - Expected: debug_current_line() equals `10`
4. debug set current location
   - Expected: debug_current_line() equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_step_mode(2)  # StepIn

debug_set_current_location("test.spl", 10, 0)
expect(debug_current_line()).to_equal(10)

debug_set_current_location("test.spl", 11, 0)
expect(debug_current_line()).to_equal(11)
```

</details>

#### maintains breakpoints while paused

1. debug set active
2. debug add breakpoint
3. debug pause
   - Expected: debug_has_breakpoint("test.spl", 10) is true
   - Expected: debug_is_paused() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_add_breakpoint("test.spl", 10, 1)
debug_pause()

expect(debug_has_breakpoint("test.spl", 10)).to_equal(true)
expect(debug_is_paused()).to_equal(true)
```

</details>

#### tracks location with active breakpoints

1. debug set active
2. debug set step mode
3. debug add breakpoint
4. debug set current location
   - Expected: debug_should_break() is false
5. debug set current location
   - Expected: debug_should_break() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
debug_set_active(true)
debug_set_step_mode(0)
debug_add_breakpoint("test.spl", 42, 1)

debug_set_current_location("test.spl", 41, 0)
expect(debug_should_break()).to_equal(false)

debug_set_current_location("test.spl", 42, 0)
expect(debug_should_break()).to_equal(true)
```

</details>

#### handles full debug session lifecycle

1. debug set active
   - Expected: debug_is_active() is true
2. debug add breakpoint
3. debug set current location
   - Expected: debug_should_break() is true
4. debug pause
   - Expected: debug_is_paused() is true
   - Expected: debug_current_file() equals `test.spl`
   - Expected: debug_current_line() equals `20`
5. debug continue
   - Expected: debug_is_paused() is false
6. debug set active
   - Expected: debug_is_active() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Activate
debug_set_active(true)
expect(debug_is_active()).to_equal(true)

# Set breakpoint
debug_add_breakpoint("test.spl", 20, 1)

# Execute to breakpoint
debug_set_current_location("test.spl", 20, 0)
expect(debug_should_break()).to_equal(true)

# Pause at breakpoint
debug_pause()
expect(debug_is_paused()).to_equal(true)

# Inspect state (location, stack, etc.)
expect(debug_current_file()).to_equal("test.spl")
expect(debug_current_line()).to_equal(20)

# Continue
debug_continue()
expect(debug_is_paused()).to_equal(false)

# Deactivate
debug_set_active(false)
expect(debug_is_active()).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
