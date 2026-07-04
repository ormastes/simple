# Coordinator Extended Specification

> 1. var backend = MockBackend create

<!-- sdn-diagram:id=coordinator_extended_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=coordinator_extended_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

coordinator_extended_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=coordinator_extended_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 23 | 23 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Coordinator Extended Specification

## Scenarios

### MockBackend lifecycle

#### attach and run

#### full lifecycle: attach -> run -> pause -> resume -> detach

1. var backend = MockBackend create
2. backend attach
   - Expected: backend.attached is true
3. backend run
   - Expected: backend.running is true
4. backend pause
   - Expected: backend.paused is true
   - Expected: backend.running is false
5. backend resume
   - Expected: backend.running is true
   - Expected: backend.paused is false
6. backend detach
   - Expected: backend.attached is false
   - Expected: backend.running is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
backend.attach("prog.spl", [])
expect(backend.attached).to_equal(true)
backend.run()
expect(backend.running).to_equal(true)
backend.pause()
expect(backend.paused).to_equal(true)
expect(backend.running).to_equal(false)
backend.resume()
expect(backend.running).to_equal(true)
expect(backend.paused).to_equal(false)
backend.detach()
expect(backend.attached).to_equal(false)
expect(backend.running).to_equal(false)
```

</details>

#### fails to run when not attached

1. var backend = MockBackend create


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
match backend.run():
    case Ok(_): fail("unexpected MockBackend result branch")
    case Err(e): expect(e).to_equal("Not attached")
```

</details>

#### error injection

#### failing backend returns attach error

1. var backend = MockBackend failing


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.failing("fail")
match backend.attach("prog.spl", []):
    case Ok(_): fail("unexpected MockBackend result branch")
    case Err(e): expect(e.contains("Attach failed")).to_equal(true)
```

</details>

#### failing backend returns run error after forced attach

1. var backend = MockBackend failing
2. backend attach


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.failing("fail")
backend.fail_attach = false
backend.attach("prog.spl", [])
match backend.run():
    case Ok(_): fail("unexpected MockBackend result branch")
    case Err(e): expect(e.contains("Run failed")).to_equal(true)
```

</details>

### MockBackend stepping

#### step modes are independent

1. var backend = MockBackend create
2. backend step over
   - Expected: backend.last_step_mode equals `over`
3. backend step in
   - Expected: backend.last_step_mode equals `in`
4. backend step out
   - Expected: backend.last_step_mode equals `out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
backend.step_over()
expect(backend.last_step_mode).to_equal("over")
backend.step_in()
expect(backend.last_step_mode).to_equal("in")
backend.step_out()
expect(backend.last_step_mode).to_equal("out")
```

</details>

#### step count accumulates correctly

1. var backend = MockBackend create
2. backend step over
3. backend step over
4. backend step in
5. backend step out
6. backend step over
   - Expected: backend.step_count equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
backend.step_over()
backend.step_over()
backend.step_in()
backend.step_out()
backend.step_over()
expect(backend.step_count).to_equal(5)
```

</details>

### MockBackend breakpoints

#### adds breakpoints with increasing ids

1. var backend = MockBackend create


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
match backend.add_breakpoint("test.spl", 10):
    case Ok(id1):
        match backend.add_breakpoint("test.spl", 20):
            case Ok(id2): expect(id2 > id1).to_equal(true)
            case Err(_): fail("unexpected MockBackend result branch")
    case Err(_): fail("unexpected MockBackend result branch")
```

</details>

#### removes specific breakpoint

1. var backend = MockBackend create
2. backend add breakpoint
3. backend add breakpoint
4. backend add breakpoint
5. backend remove breakpoint
   - Expected: backend.breakpoints.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
backend.add_breakpoint("test.spl", 10)
backend.add_breakpoint("test.spl", 20)
backend.add_breakpoint("test.spl", 30)
backend.remove_breakpoint("test.spl", 20)
expect(backend.breakpoints.len()).to_equal(2)
```

</details>

#### remove non-existent breakpoint is safe

1. var backend = MockBackend create
2. backend add breakpoint
3. backend remove breakpoint
   - Expected: backend.breakpoints.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
backend.add_breakpoint("test.spl", 10)
backend.remove_breakpoint("other.spl", 99)
expect(backend.breakpoints.len()).to_equal(1)
```

</details>

#### clear all breakpoints by removing each

1. var backend = MockBackend create
2. backend add breakpoint
3. backend add breakpoint
4. backend add breakpoint
5. backend remove breakpoint
6. backend remove breakpoint
7. backend remove breakpoint
   - Expected: backend.breakpoints.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var backend = MockBackend.create("test")
backend.add_breakpoint("a.spl", 1)
backend.add_breakpoint("b.spl", 2)
backend.add_breakpoint("c.spl", 3)
backend.remove_breakpoint("a.spl", 1)
backend.remove_breakpoint("b.spl", 2)
backend.remove_breakpoint("c.spl", 3)
expect(backend.breakpoints.len()).to_equal(0)
```

</details>

### MockBackend inspection

#### stack trace

#### returns three frames

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = MockBackend.create("test")
match backend.stack_trace():
    case Ok(frames):
        expect(frames.len()).to_equal(3)
    case Err(_): fail("unexpected MockBackend result branch")
```

</details>

#### frames have correct indices

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = MockBackend.create("test")
match backend.stack_trace():
    case Ok(frames):
        expect(frames[0].index).to_equal(0)
        expect(frames[1].index).to_equal(1)
        expect(frames[2].index).to_equal(2)
    case Err(_): fail("unexpected MockBackend result branch")
```

</details>

#### frames span multiple files

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = MockBackend.create("test")
match backend.stack_trace():
    case Ok(frames):
        expect(frames[0].file).to_equal("test.spl")
        expect(frames[2].file).to_equal("lib.spl")
    case Err(_): fail("unexpected MockBackend result branch")
```

</details>

#### locals

#### returns three variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = MockBackend.create("test")
match backend.locals():
    case Ok(vars):
        expect(vars.len()).to_equal(3)
    case Err(_): fail("unexpected MockBackend result branch")
```

</details>

#### variables have correct types

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = MockBackend.create("test")
match backend.locals():
    case Ok(vars):
        expect(vars[0].type_name).to_equal("Int")
        expect(vars[1].type_name).to_equal("String")
        expect(vars[2].type_name).to_equal("Bool")
    case Err(_): fail("unexpected MockBackend result branch")
```

</details>

#### variables have correct values

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = MockBackend.create("test")
match backend.locals():
    case Ok(vars):
        expect(vars[0].value).to_equal("42")
        expect(vars[1].value).to_equal("Alice")
    case Err(_): fail("unexpected MockBackend result branch")
```

</details>

#### evaluate

#### evaluates simple expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = MockBackend.create("test")
match backend.evaluate("x + 1"):
    case Ok(result): expect(result).to_contain("x + 1")
    case Err(_): fail("unexpected MockBackend result branch")
```

</details>

#### returns error for error expression

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = MockBackend.create("test")
match backend.evaluate("error"):
    case Ok(_): fail("unexpected MockBackend result branch")
    case Err(e): expect(e).to_contain("Evaluation failed")
```

</details>

#### location

#### returns current file and line

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = MockBackend.create("test")
match backend.current_location():
    case Ok(loc):
        expect(loc.file).to_equal("test.spl")
        expect(loc.line).to_equal(5)
        expect(loc.function_name).to_equal("main")
    case Err(_): fail("unexpected MockBackend result branch")
```

</details>

#### location has zero column default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = MockBackend.create("test")
match backend.current_location():
    case Ok(loc): expect(loc.column).to_equal(0)
    case Err(_): fail("unexpected MockBackend result branch")
```

</details>

### FrameInfo

#### creates with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f = FrameInfo.of(3, "process", "worker.spl", 99)
expect(f.index).to_equal(3)
expect(f.function_name).to_equal("process")
expect(f.file).to_equal("worker.spl")
expect(f.line).to_equal(99)
expect(f.column).to_equal(0)
```

</details>

### VarInfo

#### stores name value and type

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val v = VarInfo.of("counter", "100", "Int")
expect(v.name).to_equal("counter")
expect(v.value).to_equal("100")
expect(v.type_name).to_equal("Int")
```

</details>

### LocationInfo

#### stores file line and function

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val loc = LocationInfo.at("app.spl", 42, "handle_request")
expect(loc.file).to_equal("app.spl")
expect(loc.line).to_equal(42)
expect(loc.function_name).to_equal("handle_request")
expect(loc.column).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/coordinator_extended_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MockBackend lifecycle
- MockBackend stepping
- MockBackend breakpoints
- MockBackend inspection
- FrameInfo
- VarInfo
- LocationInfo

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 23 |
| Active scenarios | 23 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
