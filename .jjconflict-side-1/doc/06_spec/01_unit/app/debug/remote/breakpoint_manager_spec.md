# Breakpoint Manager Specification

> <details>

<!-- sdn-diagram:id=breakpoint_manager_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=breakpoint_manager_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

breakpoint_manager_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=breakpoint_manager_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Breakpoint Manager Specification

## Scenarios

### BreakpointInfo

### construction with of()

#### creates a breakpoint with id, file, and line

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = BreakpointInfo.of(1, "main.spl", 42)
expect(bp.id).to_equal(1)
expect(bp.file).to_equal("main.spl")
expect(bp.line).to_equal(42)
```

</details>

#### sets enabled to true by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = BreakpointInfo.of(1, "main.spl", 42)
expect(bp.enabled).to_equal(true)
```

</details>

#### sets condition to empty by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = BreakpointInfo.of(1, "main.spl", 42)
expect(bp.condition).to_equal("")
```

</details>

#### sets hit_count to 0 by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = BreakpointInfo.of(1, "main.spl", 42)
expect(bp.hit_count).to_equal(0)
```

</details>

#### sets is_temporary to false by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = BreakpointInfo.of(1, "main.spl", 42)
expect(bp.is_temporary).to_equal(false)
```

</details>

#### sets log_message to empty by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = BreakpointInfo.of(1, "main.spl", 42)
expect(bp.log_message).to_equal("")
```

</details>

#### sets func_name to empty by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = BreakpointInfo.of(1, "main.spl", 42)
expect(bp.func_name).to_equal("")
```

</details>

#### sets address to 0 by default

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = BreakpointInfo.of(1, "main.spl", 42)
expect(bp.address).to_equal(0)
```

</details>

### construction with function_bp()

#### creates a function breakpoint with func_name

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = BreakpointInfo.function_bp(2, "main")
expect(bp.id).to_equal(2)
expect(bp.func_name).to_equal("main")
```

</details>

#### sets file to empty for function breakpoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = BreakpointInfo.function_bp(2, "main")
expect(bp.file).to_equal("")
```

</details>

#### sets line to 0 for function breakpoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = BreakpointInfo.function_bp(2, "main")
expect(bp.line).to_equal(0)
```

</details>

#### sets enabled to true for function breakpoints

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = BreakpointInfo.function_bp(3, "calculate")
expect(bp.enabled).to_equal(true)
```

</details>

### to_string()

#### formats a basic line breakpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = BreakpointInfo.of(1, "main.spl", 42)
val s = bp.to_string()
expect(s).to_contain("bp#1")
expect(s).to_contain("main.spl:42")
```

</details>

#### formats a function breakpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = BreakpointInfo.function_bp(2, "main")
val s = bp.to_string()
expect(s).to_contain("bp#2")
expect(s).to_contain("fn:main")
```

</details>

#### shows disabled state

1. var bp = BreakpointInfo of


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bp = BreakpointInfo.of(1, "main.spl", 10)
bp.enabled = false
val s = bp.to_string()
expect(s).to_contain("[disabled]")
```

</details>

#### shows condition

1. var bp = BreakpointInfo of


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bp = BreakpointInfo.of(1, "main.spl", 10)
bp.condition = "x > 5"
val s = bp.to_string()
expect(s).to_contain("if:x > 5")
```

</details>

#### shows hit count when non-zero

1. var bp = BreakpointInfo of


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bp = BreakpointInfo.of(1, "main.spl", 10)
bp.hit_count = 3
val s = bp.to_string()
expect(s).to_contain("hits:3")
```

</details>

#### does not show hit count when zero

1. var has hits = s contains
   - Expected: has_hits is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = BreakpointInfo.of(1, "main.spl", 10)
val s = bp.to_string()
expect(s).to_start_with("bp#1")
# Should not contain "hits:" since hit_count is 0
var has_hits = s.contains("hits:")
expect(has_hits).to_equal(false)
```

</details>

#### shows temporary flag

1. var bp = BreakpointInfo of


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bp = BreakpointInfo.of(1, "main.spl", 10)
bp.is_temporary = true
val s = bp.to_string()
expect(s).to_contain("[temp]")
```

</details>

#### shows log message

1. var bp = BreakpointInfo of


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bp = BreakpointInfo.of(1, "main.spl", 10)
bp.log_message = "reached here"
val s = bp.to_string()
expect(s).to_contain("log:reached here")
```

</details>

#### combines multiple attributes

1. var bp = BreakpointInfo of


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bp = BreakpointInfo.of(5, "test.spl", 100)
bp.condition = "i == 10"
bp.hit_count = 7
bp.is_temporary = true
val s = bp.to_string()
expect(s).to_contain("bp#5")
expect(s).to_contain("test.spl:100")
expect(s).to_contain("if:i == 10")
expect(s).to_contain("hits:7")
expect(s).to_contain("[temp]")
```

</details>

### serialize()

#### serializes a basic breakpoint with pipe delimiters

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = BreakpointInfo.of(1, "main.spl", 42)
val s = bp.serialize()
expect(s).to_equal("1|main.spl|42||1|0|0|||0")
```

</details>

#### serializes a disabled breakpoint

1. var bp = BreakpointInfo of


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bp = BreakpointInfo.of(1, "main.spl", 42)
bp.enabled = false
val s = bp.serialize()
expect(s).to_contain("|0|0|0|")
```

</details>

#### serializes a temporary breakpoint

1. var bp = BreakpointInfo of
   - Expected: s equals `1|main.spl|42||1|0|1|||0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bp = BreakpointInfo.of(1, "main.spl", 42)
bp.is_temporary = true
val s = bp.serialize()
expect(s).to_equal("1|main.spl|42||1|0|1|||0")
```

</details>

#### serializes a conditional breakpoint

1. var bp = BreakpointInfo of
   - Expected: s equals `1|main.spl|42|x > 10|1|0|0|||0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bp = BreakpointInfo.of(1, "main.spl", 42)
bp.condition = "x > 10"
val s = bp.serialize()
expect(s).to_equal("1|main.spl|42|x > 10|1|0|0|||0")
```

</details>

#### serializes a function breakpoint

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bp = BreakpointInfo.function_bp(3, "process")
val s = bp.serialize()
expect(s).to_equal("3||0||1|0|0||process|0")
```

</details>

#### serializes with hit count

1. var bp = BreakpointInfo of


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bp = BreakpointInfo.of(2, "test.spl", 10)
bp.hit_count = 15
val s = bp.serialize()
expect(s).to_contain("|15|")
```

</details>

#### serializes with log message

1. var bp = BreakpointInfo of


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bp = BreakpointInfo.of(1, "main.spl", 5)
bp.log_message = "checkpoint reached"
val s = bp.serialize()
expect(s).to_contain("checkpoint reached")
```

</details>

#### serializes with address

1. var bp = BreakpointInfo of


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bp = BreakpointInfo.of(1, "main.spl", 5)
bp.address = 4096
val s = bp.serialize()
expect(s).to_end_with("|4096")
```

</details>

### field mutation

#### can modify enabled state

1. var bp = BreakpointInfo of
   - Expected: bp.enabled is true
   - Expected: bp.enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bp = BreakpointInfo.of(1, "main.spl", 10)
expect(bp.enabled).to_equal(true)
bp.enabled = false
expect(bp.enabled).to_equal(false)
```

</details>

#### can modify condition

1. var bp = BreakpointInfo of
   - Expected: bp.condition equals `count > 100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bp = BreakpointInfo.of(1, "main.spl", 10)
bp.condition = "count > 100"
expect(bp.condition).to_equal("count > 100")
```

</details>

#### can modify hit_count

1. var bp = BreakpointInfo of
   - Expected: bp.hit_count equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bp = BreakpointInfo.of(1, "main.spl", 10)
bp.hit_count = 42
expect(bp.hit_count).to_equal(42)
```

</details>

#### can modify log_message

1. var bp = BreakpointInfo of
   - Expected: bp.log_message equals `debug point`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var bp = BreakpointInfo.of(1, "main.spl", 10)
bp.log_message = "debug point"
expect(bp.log_message).to_equal("debug point")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/debug/remote/breakpoint_manager_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- BreakpointInfo
- construction with of()
- construction with function_bp()
- to_string()
- serialize()
- field mutation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
