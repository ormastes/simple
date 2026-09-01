# Debug State Specification

> Tests covering DebugState to_string, DebugState description, DebugState is_stopped, DebugState is_running, DebugState is_paused, DebugState is_terminated, DebugState is_active, DebugState is_halted, DebugState can_continue, DebugState summary.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Debug State Specification

## Scenarios

### DebugState to_string

#### converts Stopped to string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- converts Stopped to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Stopped to string")
# Branch: case Stopped: "stopped"
val state = "stopped"
expect(state == "stopped")
```

</details>

#### converts Running to string

- converts Running to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Running to string")
# Branch: case Running: "running"
val state = "running"
expect(state == "running")
```

</details>

#### converts Paused to string

- converts Paused to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Paused to string")
# Branch: case Paused: "paused"
val state = "paused"
expect(state == "paused")
```

</details>

#### converts Terminated to string

- converts Terminated to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts Terminated to string")
# Branch: case Terminated: "terminated"
val state = "terminated"
expect(state == "terminated")
```

</details>

### DebugState description

#### describes Stopped

- describes Stopped


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Stopped")
# Branch: case Stopped: "Debugger stopped at breakpoint"
val desc = "Debugger stopped at breakpoint"
expect(desc == "Debugger stopped at breakpoint")
```

</details>

#### describes Running

- describes Running


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Running")
# Branch: case Running: "Program executing"
val desc = "Program executing"
expect(desc == "Program executing")
```

</details>

#### describes Paused

- describes Paused


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Paused")
# Branch: case Paused: "Execution paused by user"
val desc = "Execution paused by user"
expect(desc == "Execution paused by user")
```

</details>

#### describes Terminated

- describes Terminated


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("describes Terminated")
# Branch: case Terminated: "Program terminated"
val desc = "Program terminated"
expect(desc == "Program terminated")
```

</details>

### DebugState is_stopped

#### returns true for Stopped

- returns true for Stopped


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Stopped")
# Branch: case Stopped: true
val is_stopped = true
expect(is_stopped)
```

</details>

#### returns false for other states

- returns false for other states


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for other states")
# Branch: case _: false
val is_stopped = false
expect(not is_stopped)
```

</details>

### DebugState is_running

#### returns true for Running

- returns true for Running


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Running")
# Branch: case Running: true
val is_running = true
expect(is_running)
```

</details>

#### returns false for other states

- returns false for other states


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for other states")
# Branch: case _: false
val is_running = false
expect(not is_running)
```

</details>

### DebugState is_paused

#### returns true for Paused

- returns true for Paused


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Paused")
# Branch: case Paused: true
val is_paused = true
expect(is_paused)
```

</details>

#### returns false for other states

- returns false for other states


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for other states")
# Branch: case _: false
val is_paused = false
expect(not is_paused)
```

</details>

### DebugState is_terminated

#### returns true for Terminated

- returns true for Terminated


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Terminated")
# Branch: case Terminated: true
val is_terminated = true
expect(is_terminated)
```

</details>

#### returns false for other states

- returns false for other states


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for other states")
# Branch: case _: false
val is_terminated = false
expect(not is_terminated)
```

</details>

### DebugState is_active

#### returns false for Terminated

- returns false for Terminated


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for Terminated")
# Branch: case Terminated: false
val is_active = false
expect(not is_active)
```

</details>

#### returns true for other states

- returns true for other states


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for other states")
# Branch: case _: true
val is_active = true
expect(is_active)
```

</details>

### DebugState is_halted

#### returns true for Stopped

- returns true for Stopped


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Stopped")
# Branch: case Stopped: true
val is_halted = true
expect(is_halted)
```

</details>

#### returns true for Paused

- returns true for Paused


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns true for Paused")
# Branch: case Paused: true
val is_halted = true
expect(is_halted)
```

</details>

#### returns false for other states

- returns false for other states


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for other states")
# Branch: case _: false
val is_halted = false
expect(not is_halted)
```

</details>

### DebugState can_continue

#### delegates to is_halted

- delegates to is_halted


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("delegates to is_halted")
# Branch: return self.is_halted()
val can_continue = true
expect(can_continue)
```

</details>

### DebugState summary

#### categorizes as halted when active and halted

- categorizes as halted when active and halted


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes as halted when active and halted")
# Branch: if self.is_active() and self.is_halted()
val status = "halted"
expect(status == "halted")
```

</details>

#### categorizes as executing when active and not halted

- categorizes as executing when active and not halted


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes as executing when active and not halted")
# Branch: if self.is_active() and not self.is_halted()
val status = "executing"
expect(status == "executing")
```

</details>

#### categorizes as terminated when not active

- categorizes as terminated when not active


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("categorizes as terminated when not active")
# Branch: else (not active)
val status = "terminated"
expect(status == "terminated")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/dap/debug_state_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DebugState to_string, DebugState description, DebugState is_stopped, DebugState is_running, DebugState is_paused, DebugState is_terminated, DebugState is_active, DebugState is_halted, DebugState can_continue, DebugState summary.
- DebugState to_string
- DebugState description
- DebugState is_stopped
- DebugState is_running
- DebugState is_paused
- DebugState is_terminated
- DebugState is_active
- DebugState is_halted
- DebugState can_continue
- DebugState summary

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c415bf2a84744a38c2f535cda0c141bdccc78ce6e0254ce4fe9754b1577f6452`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c415bf2a84744a38c2f535cda0c141bdccc78ce6e0254ce4fe9754b1577f6452`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c415bf2a84744a38c2f535cda0c141bdccc78ce6e0254ce4fe9754b1577f6452`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/dap/debug_state_spec.spl
mirror: doc/06_spec/unit/app/dap/debug_state_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/dap/debug_state_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/dap/debug_state_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/dap/debug_state_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts Stopped to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/dap/debug_state_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts Running to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/dap/debug_state_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts Paused to string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
