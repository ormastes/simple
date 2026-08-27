# Debug Boot with GDB Integration

> Tests debug-enabled boot sequences with GDB integration using a self-contained harness. Models the QEMU/GDB flow with local doubles to verify debug boot configuration, breakpoint placement, and symbol loading.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests debug-enabled boot sequences with GDB integration using a self-contained
harness. Models the QEMU/GDB flow with local doubles to verify debug boot
configuration, breakpoint placement, and symbol loading.

## Scenarios

### Debug Connection

#### can connect when qemu and gdb are available

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- can connect when qemu and gdb are available


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("can connect when qemu and gdb are available")
val session = DebugSession.create("x86", true, true)
check(session.can_connect())
check(session.connect())
check(session.connected)
```

</details>

#### does not connect when qemu is missing

- does not connect when qemu is missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not connect when qemu is missing")
val session = DebugSession.create("x86", false, true)
check(not session.can_connect())
check(not session.connect())
```

</details>

#### does not connect when gdb is missing

- does not connect when gdb is missing


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("does not connect when gdb is missing")
val session = DebugSession.create("x86", true, false)
check(not session.can_connect())
check(not session.connect())
```

</details>

#### reads registers after connection

- reads registers after connection


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads registers after connection")
val session = DebugSession.create("x86", true, true)
session.connect()
check(session.read_registers().contains("pc=0x1000"))
check(session.read_registers().contains("sp=0x2000"))
```

</details>

### Crash Analysis

#### detects null pointer crashes

- detects null pointer crashes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects null pointer crashes")
val session = DebugSession.create("x86", true, true)
session.capture_crash("null_pointer")
check(session.analyze_crash().contains("null_pointer"))
check(session.analyze_crash().contains("stack:main"))
```

</details>

#### extracts stack traces

- extracts stack traces


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts stack traces")
val session = DebugSession.create("arm", true, true)
session.capture_crash("stack_overflow")
check(session.analyze_crash().contains("stack_overflow"))
check(session.analyze_crash().contains("debug_boot"))
```

</details>

#### shows register state on crash

- shows register state on crash


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("shows register state on crash")
val session = DebugSession.create("riscv", true, true)
session.connect()
session.capture_crash("illegal_instruction")
check(session.read_registers().contains("pc=0x1000"))
check(session.analyze_crash().contains("illegal_instruction"))
```

</details>

### Debug Output

#### formats debug info

- formats debug info


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats debug info")
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

- supports x86 targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports x86 targets")
val session = DebugSession.create("x86", true, true)
check(session.target == "x86")
check(session.can_connect())
```

</details>

#### supports ARM targets

- supports ARM targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports ARM targets")
val session = DebugSession.create("arm", true, true)
check(session.target == "arm")
check(session.can_connect())
```

</details>

#### supports RISC-V targets

- supports RISC-V targets


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports RISC-V targets")
val session = DebugSession.create("riscv", true, true)
check(session.target == "riscv")
check(session.can_connect())
```

</details>

### Breakpoint Management

#### stores multiple breakpoints

- stores multiple breakpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("stores multiple breakpoints")
val session = DebugSession.create("x86", true, true)
session.add_breakpoint("entry")
session.add_breakpoint("panic")
check(session.has_breakpoint("entry"))
check(session.has_breakpoint("panic"))
```

</details>

#### continues after a breakpoint

- continues after a breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("continues after a breakpoint")
val session = DebugSession.create("x86", true, true)
session.connect()
session.add_breakpoint("entry")
check(session.single_step())
check(session.step_count == 1)
```

</details>

### Single-Step Debugging

#### single-steps through code

- single-steps through code


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("single-steps through code")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `acd4e73c85b8b1e077feab40a2ed0ccbf001c46c0fec2f5f7e1dd00106746cf4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `acd4e73c85b8b1e077feab40a2ed0ccbf001c46c0fec2f5f7e1dd00106746cf4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `acd4e73c85b8b1e077feab40a2ed0ccbf001c46c0fec2f5f7e1dd00106746cf4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/03_system/feature/baremetal/debug_boot_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/debug_boot_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/baremetal/debug_boot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/debug_boot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/debug_boot_spec.spl:91:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can connect when qemu and gdb are available' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/baremetal/debug_boot_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can connect when qemu and gdb are available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/debug_boot_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not connect when qemu is missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/debug_boot_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not connect when gdb is missing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
