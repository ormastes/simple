# Debug Coordinator Specification

> <details>

<!-- sdn-diagram:id=debug_coordinator_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=debug_coordinator_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

debug_coordinator_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=debug_coordinator_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Debug Coordinator Specification

## Scenarios

### FrameInfo

#### creates frame info

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = FrameInfo.of(0, "main", "test.spl", 42)
expect(frame.index).to_equal(0)
expect(frame.function_name).to_equal("main")
expect(frame.file).to_equal("test.spl")
expect(frame.line).to_equal(42)
expect(frame.column).to_equal(0)
```

</details>

### VarInfo

#### creates variable info

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = VarInfo.of("count", "10", "Int")
expect(v.name).to_equal("count")
expect(v.value).to_equal("10")
expect(v.type_name).to_equal("Int")
```

</details>

### LocationInfo

#### creates location info

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = LocationInfo.at("main.spl", 15, "run")
expect(loc.file).to_equal("main.spl")
expect(loc.line).to_equal(15)
expect(loc.function_name).to_equal("run")
```

</details>

### MockBackend

#### lifecycle

#### starts detached

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = MockBackend.create("test")
expect(backend.attached).to_equal(false)
expect(backend.running).to_equal(false)
```

</details>

#### attaches successfully

1. var backend = MockBackend create


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
match backend.attach("prog.spl", []):
    case Ok(_): expect(backend.attached).to_equal(true)
    case Err(_): fail("MockBackend.attach returned Err for a valid program")
```

</details>

#### runs after attach

1. var backend = MockBackend create
2. backend attach


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
backend.attach("prog.spl", [])
match backend.run():
    case Ok(_): expect(backend.running).to_equal(true)
    case Err(_): fail("MockBackend.run returned Err after attach")
```

</details>

#### fails to run without attach

1. var backend = MockBackend create


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
match backend.run():
    case Ok(_): fail("MockBackend.run unexpectedly succeeded before attach")
    case Err(e): expect(e).to_equal("Not attached")
```

</details>

#### detaches cleanly

1. var backend = MockBackend create
2. backend attach
3. backend run
4. backend detach
   - Expected: backend.attached is false
   - Expected: backend.running is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
backend.attach("prog.spl", [])
backend.run()
backend.detach()
expect(backend.attached).to_equal(false)
expect(backend.running).to_equal(false)
```

</details>

#### execution control

#### pauses running program

1. var backend = MockBackend create
2. backend attach
3. backend run
4. backend pause
   - Expected: backend.paused is true
   - Expected: backend.running is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
backend.attach("prog.spl", [])
backend.run()
backend.pause()
expect(backend.paused).to_equal(true)
expect(backend.running).to_equal(false)
```

</details>

#### resumes paused program

1. var backend = MockBackend create
2. backend attach
3. backend run
4. backend pause
5. backend resume
   - Expected: backend.paused is false
   - Expected: backend.running is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
backend.attach("prog.spl", [])
backend.run()
backend.pause()
backend.resume()
expect(backend.paused).to_equal(false)
expect(backend.running).to_equal(true)
```

</details>

#### stepping

#### tracks step over

1. var backend = MockBackend create
2. backend step over
   - Expected: backend.step_count equals `1`
   - Expected: backend.last_step_mode equals `over`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
backend.step_over()
expect(backend.step_count).to_equal(1)
expect(backend.last_step_mode).to_equal("over")
```

</details>

#### tracks step in

1. var backend = MockBackend create
2. backend step in
   - Expected: backend.last_step_mode equals `in`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
backend.step_in()
expect(backend.last_step_mode).to_equal("in")
```

</details>

#### tracks step out

1. var backend = MockBackend create
2. backend step out
   - Expected: backend.last_step_mode equals `out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
backend.step_out()
expect(backend.last_step_mode).to_equal("out")
```

</details>

#### accumulates step count

1. var backend = MockBackend create
2. backend step over
3. backend step in
4. backend step out
   - Expected: backend.step_count equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
backend.step_over()
backend.step_in()
backend.step_out()
expect(backend.step_count).to_equal(3)
```

</details>

#### breakpoints

#### adds breakpoints

1. var backend = MockBackend create
2. backend add breakpoint
   - Expected: backend.breakpoints.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
backend.add_breakpoint("test.spl", 10)
expect(backend.breakpoints.len()).to_equal(1)
```

</details>

#### adds multiple breakpoints

1. var backend = MockBackend create
2. backend add breakpoint
3. backend add breakpoint
4. backend add breakpoint
   - Expected: backend.breakpoints.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
backend.add_breakpoint("test.spl", 10)
backend.add_breakpoint("test.spl", 20)
backend.add_breakpoint("other.spl", 5)
expect(backend.breakpoints.len()).to_equal(3)
```

</details>

#### removes breakpoints

1. var backend = MockBackend create
2. backend add breakpoint
3. backend add breakpoint
4. backend remove breakpoint
   - Expected: backend.breakpoints.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
backend.add_breakpoint("test.spl", 10)
backend.add_breakpoint("test.spl", 20)
backend.remove_breakpoint("test.spl", 10)
expect(backend.breakpoints.len()).to_equal(1)
```

</details>

#### inspection

#### returns stack trace

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = MockBackend.create("test")
match backend.stack_trace():
    case Ok(frames):
        expect(frames.len()).to_equal(2)
        expect(frames[0].function_name).to_equal("main")
        expect(frames[1].function_name).to_equal("helper")
    case Err(_):
        fail("MockBackend.stack_trace returned Err")
```

</details>

#### returns local variables

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = MockBackend.create("test")
match backend.locals():
    case Ok(vars):
        expect(vars.len()).to_equal(2)
        expect(vars[0].name).to_equal("x")
        expect(vars[0].value).to_equal("42")
        expect(vars[1].name).to_equal("name")
    case Err(_):
        fail("MockBackend.locals returned Err")
```

</details>

#### evaluates expressions

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = MockBackend.create("test")
match backend.evaluate("x + 1"):
    case Ok(result):
        expect(result).to_contain("x + 1")
    case Err(_):
        fail("MockBackend.evaluate returned Err")
```

</details>

#### returns current location

1. fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = MockBackend.create("test")
match backend.current_location():
    case Ok(loc):
        expect(loc.file).to_equal("test.spl")
        expect(loc.line).to_equal(5)
        expect(loc.function_name).to_equal("main")
    case Err(_):
        fail("MockBackend.current_location returned Err")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/debug_coordinator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- FrameInfo
- VarInfo
- LocationInfo
- MockBackend

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
