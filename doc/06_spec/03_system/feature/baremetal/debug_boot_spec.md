# Debug Boot with GDB Integration

> Tests debug-enabled boot sequences with GDB integration using a self-contained harness. Models the QEMU/GDB flow with local doubles to verify debug boot configuration, breakpoint placement, and symbol loading.

<!-- sdn-diagram:id=debug_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=debug_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

debug_boot_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=debug_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Debug Boot with GDB Integration

Tests debug-enabled boot sequences with GDB integration using a self-contained harness. Models the QEMU/GDB flow with local doubles to verify debug boot configuration, breakpoint placement, and symbol loading.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/debug_boot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests debug-enabled boot sequences with GDB integration using a self-contained
harness. Models the QEMU/GDB flow with local doubles to verify debug boot
configuration, breakpoint placement, and symbol loading.

## Scenarios

### Debug Connection

#### can connect when qemu and gdb are available

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = DebugSession.create("x86", true, true)
check(session.can_connect())
check(session.connect())
check(session.connected)
```

</details>

#### does not connect when qemu is missing

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = DebugSession.create("x86", false, true)
check(not session.can_connect())
check(not session.connect())
```

</details>

#### does not connect when gdb is missing

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = DebugSession.create("x86", true, false)
check(not session.can_connect())
check(not session.connect())
```

</details>

#### reads registers after connection

1. session connect
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = DebugSession.create("x86", true, true)
session.connect()
check(session.read_registers().contains("pc=0x1000"))
check(session.read_registers().contains("sp=0x2000"))
```

</details>

### Crash Analysis

#### detects null pointer crashes

1. session capture crash
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = DebugSession.create("x86", true, true)
session.capture_crash("null_pointer")
check(session.analyze_crash().contains("null_pointer"))
check(session.analyze_crash().contains("stack:main"))
```

</details>

#### extracts stack traces

1. session capture crash
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = DebugSession.create("arm", true, true)
session.capture_crash("stack_overflow")
check(session.analyze_crash().contains("stack_overflow"))
check(session.analyze_crash().contains("debug_boot"))
```

</details>

#### shows register state on crash

1. session connect
2. session capture crash
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = DebugSession.create("riscv", true, true)
session.connect()
session.capture_crash("illegal_instruction")
check(session.read_registers().contains("pc=0x1000"))
check(session.analyze_crash().contains("illegal_instruction"))
```

</details>

### Debug Output

#### formats debug info

1. session connect
2. session add breakpoint
3. session single step
4. check
5. check
6. check
7. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = DebugSession.create("x86", true, true)
session.connect()
session.add_breakpoint("entry")
session.single_step()
check(session.debug_info().contains("target=x86"))
check(session.debug_info().contains("connected=true"))
check(session.debug_info().contains("bps=1"))
check(session.debug_info().contains("steps=1"))
```

</details>

### Multi-Architecture Debug

#### supports x86 targets

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = DebugSession.create("x86", true, true)
check(session.target == "x86")
check(session.can_connect())
```

</details>

#### supports ARM targets

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = DebugSession.create("arm", true, true)
check(session.target == "arm")
check(session.can_connect())
```

</details>

#### supports RISC-V targets

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = DebugSession.create("riscv", true, true)
check(session.target == "riscv")
check(session.can_connect())
```

</details>

### Breakpoint Management

#### stores multiple breakpoints

1. session add breakpoint
2. session add breakpoint
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = DebugSession.create("x86", true, true)
session.add_breakpoint("entry")
session.add_breakpoint("panic")
check(session.has_breakpoint("entry"))
check(session.has_breakpoint("panic"))
```

</details>

#### continues after a breakpoint

1. session connect
2. session add breakpoint
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = DebugSession.create("x86", true, true)
session.connect()
session.add_breakpoint("entry")
check(session.single_step())
check(session.step_count == 1)
```

</details>

### Single-Step Debugging

#### single-steps through code

1. session connect
2. check
3. check
4. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val session = DebugSession.create("x86", true, true)
session.connect()
check(session.single_step())
check(session.single_step())
check(session.step_count == 2)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
