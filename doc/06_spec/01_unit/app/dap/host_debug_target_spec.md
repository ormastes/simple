# Host Debug Target Specification

> Tests covering HostDebugTarget identity, HostDebugTarget state, HostDebugTarget breakpoints, HostDebugTarget step, HostDebugTarget resume, HostDebugTarget read_mem, HostDebugTarget detach.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Debug Target Specification

## Scenarios

### HostDebugTarget identity

#### reports the host kind

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports the host kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the host kind")
var t = HostDebugTarget.launch(FIXTURE)
assert_equal(t.kind(), "host")
```

</details>

#### reports Native debug capability

- reports Native debug capability


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports Native debug capability")
var t = HostDebugTarget.launch(FIXTURE)
assert_equal(cap_level_name(t.debug_level()), "native")
```

</details>

### HostDebugTarget state

#### starts on the first executable line with line pc units

- starts on the first executable line with line pc units


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts on the first executable line with line pc units")
var t = HostDebugTarget.launch(FIXTURE)
val s = t.state()
assert_equal(s.pc, 4)
assert_equal(s.pc_kind, "line")
assert_equal(s.stop_reason, "running")
```

</details>

#### reports a single-frame call stack at the current line

- reports a single-frame call stack at the current line


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports a single-frame call stack at the current line")
var t = HostDebugTarget.launch(FIXTURE)
val s = t.state()
assert_equal(s.call_stack.len(), 1)
assert_equal(s.call_stack[0], 4)
```

</details>

#### is a pure read that does not advance execution

- is a pure read that does not advance execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is a pure read that does not advance execution")
var t = HostDebugTarget.launch(FIXTURE)
val a = t.state()
val b = t.state()
val c = t.state()
assert_equal(a.pc, b.pc)
assert_equal(b.pc, c.pc)
assert_equal(c.pc, 4)
```

</details>

#### reports sp as the count of visible bindings

- reports sp as the count of visible bindings


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports sp as the count of visible bindings")
var t = HostDebugTarget.launch(FIXTURE)
val before = t.state().sp
t.step()
t.step()
assert_true(t.state().sp > before)
```

</details>

### HostDebugTarget breakpoints

#### reports true when a breakpoint is newly added

- reports true when a breakpoint is newly added


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports true when a breakpoint is newly added")
var t = HostDebugTarget.launch(FIXTURE)
assert_true(t.set_breakpoint(6))
assert_equal(t.breakpoints().len(), 1)
assert_equal(t.breakpoints()[0], 6)
```

</details>

#### reports false for a line that already has a breakpoint

- reports false for a line that already has a breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports false for a line that already has a breakpoint")
var t = HostDebugTarget.launch(FIXTURE)
assert_true(t.set_breakpoint(6))
assert_false(t.set_breakpoint(6))
assert_equal(t.breakpoints().len(), 1)
```

</details>

#### refuses a breakpoint past the end of the program

- refuses a breakpoint past the end of the program


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a breakpoint past the end of the program")
var t = HostDebugTarget.launch(FIXTURE)
assert_false(t.set_breakpoint(9999))
assert_equal(t.breakpoints().len(), 0)
```

</details>

#### lists breakpoints in ascending order regardless of insertion order

- lists breakpoints in ascending order regardless of insertion order


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("lists breakpoints in ascending order regardless of insertion order")
var t = HostDebugTarget.launch(FIXTURE)
assert_true(t.set_breakpoint(7))
assert_true(t.set_breakpoint(5))
assert_true(t.set_breakpoint(6))
assert_equal(t.breakpoints().len(), 3)
assert_equal(t.breakpoints()[0], 5)
assert_equal(t.breakpoints()[1], 6)
assert_equal(t.breakpoints()[2], 7)
```

</details>

#### clears a breakpoint that was set

- clears a breakpoint that was set


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears a breakpoint that was set")
var t = HostDebugTarget.launch(FIXTURE)
assert_true(t.set_breakpoint(6))
assert_true(t.clear_breakpoint(6))
assert_equal(t.breakpoints().len(), 0)
```

</details>

#### reports false when clearing a line that has no breakpoint

- reports false when clearing a line that has no breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports false when clearing a line that has no breakpoint")
var t = HostDebugTarget.launch(FIXTURE)
assert_false(t.clear_breakpoint(5))
```

</details>

#### clears only the requested line

- clears only the requested line


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears only the requested line")
var t = HostDebugTarget.launch(FIXTURE)
assert_true(t.set_breakpoint(5))
assert_true(t.set_breakpoint(6))
assert_true(t.clear_breakpoint(5))
assert_equal(t.breakpoints().len(), 1)
assert_equal(t.breakpoints()[0], 6)
```

</details>

### HostDebugTarget step

#### advances one executable line and reports the step reason

- advances one executable line and reports the step reason


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("advances one executable line and reports the step reason")
var t = HostDebugTarget.launch(FIXTURE)
val s = t.step()
assert_equal(s.pc, 5)
assert_equal(s.stop_reason, "step")
assert_true(debug_state_is_stopped_alive(s))
```

</details>

#### advances again on a second step

- advances again on a second step


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("advances again on a second step")
var t = HostDebugTarget.launch(FIXTURE)
t.step()
val s = t.step()
assert_equal(s.pc, 6)
assert_equal(s.stop_reason, "step")
```

</details>

#### is not wedged by a breakpoint on the destination line

- is not wedged by a breakpoint on the destination line


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is not wedged by a breakpoint on the destination line")
var t = HostDebugTarget.launch(FIXTURE)
assert_true(t.set_breakpoint(5))
val s = t.step()
assert_equal(s.pc, 5)
assert_equal(s.stop_reason, "step")
```

</details>

#### halts instead of advancing past the last line

- halts instead of advancing past the last line


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("halts instead of advancing past the last line")
var t = HostDebugTarget.launch(FIXTURE)
t.step()
t.step()
t.step()
val s = t.step()
assert_equal(s.pc, 7)
assert_equal(s.stop_reason, "halt")
assert_true(debug_state_is_terminal(s))
```

</details>

### HostDebugTarget resume

#### stops at the next breakpoint

- stops at the next breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops at the next breakpoint")
var t = HostDebugTarget.launch(FIXTURE)
assert_true(t.set_breakpoint(6))
val s = t.resume()
assert_equal(s.pc, 6)
assert_equal(s.stop_reason, "breakpoint")
```

</details>

#### picks the nearest breakpoint ahead of the current line

- picks the nearest breakpoint ahead of the current line


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("picks the nearest breakpoint ahead of the current line")
var t = HostDebugTarget.launch(FIXTURE)
assert_true(t.set_breakpoint(7))
assert_true(t.set_breakpoint(5))
val s = t.resume()
assert_equal(s.pc, 5)
assert_equal(s.stop_reason, "breakpoint")
```

</details>

#### makes progress when resuming from a breakpointed location

- makes progress when resuming from a breakpointed location


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("makes progress when resuming from a breakpointed location")
var t = HostDebugTarget.launch(FIXTURE)
assert_true(t.set_breakpoint(5))
assert_true(t.set_breakpoint(7))
val first = t.resume()
assert_equal(first.pc, 5)
val second = t.resume()
assert_equal(second.pc, 7)
assert_equal(second.stop_reason, "breakpoint")
```

</details>

#### halts when there is no breakpoint ahead

- halts when there is no breakpoint ahead


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("halts when there is no breakpoint ahead")
var t = HostDebugTarget.launch(FIXTURE)
val s = t.resume()
assert_equal(s.stop_reason, "halt")
assert_true(debug_state_is_terminal(s))
```

</details>

### HostDebugTarget read_mem

#### reads the head of the variable slab

- reads the head of the variable slab


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads the head of the variable slab")
var t = HostDebugTarget.launch(FIXTURE)
val bytes = t.read_mem(0, 1)
assert_equal(bytes.len(), 1)
# The slab is the session's variables body: {"variables":[...]}
assert_equal(bytes[0] as i64, 123)     # '{'
```

</details>

#### reads an in-range window of the requested length

- reads an in-range window of the requested length


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads an in-range window of the requested length")
var t = HostDebugTarget.launch(FIXTURE)
val bytes = t.read_mem(1, 4)
assert_equal(bytes.len(), 4)
assert_equal(bytes[0] as i64, 34)      # '"'
```

</details>

#### returns nothing for a non-positive length

- returns nothing for a non-positive length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nothing for a non-positive length")
var t = HostDebugTarget.launch(FIXTURE)
assert_equal(t.read_mem(0, 0).len(), 0)
```

</details>

#### returns nothing for a negative offset

- returns nothing for a negative offset


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nothing for a negative offset")
var t = HostDebugTarget.launch(FIXTURE)
assert_equal(t.read_mem(-1, 4).len(), 0)
```

</details>

#### returns empty rather than a short buffer when the read overruns

- returns empty rather than a short buffer when the read overruns


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty rather than a short buffer when the read overruns")
var t = HostDebugTarget.launch(FIXTURE)
val n = host_mem_len(t)
assert_true(n > 0)
assert_equal(t.read_mem(0, n).len(), n)
assert_equal(t.read_mem(0, n + 1).len(), 0)
assert_equal(t.read_mem(n - 1, 2).len(), 0)
```

</details>

#### grows the slab as execution reveals more variables

- grows the slab as execution reveals more variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("grows the slab as execution reveals more variables")
var t = HostDebugTarget.launch(FIXTURE)
val before = host_mem_len(t)
t.step()
t.step()
assert_true(host_mem_len(t) > before)
```

</details>

### HostDebugTarget detach

#### reports no error and drops breakpoints

- reports no error and drops breakpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no error and drops breakpoints")
var t = HostDebugTarget.launch(FIXTURE)
assert_true(t.set_breakpoint(6))
assert_equal(t.detach(), "")
assert_equal(t.breakpoints().len(), 0)
```

</details>

#### is safe to call twice

- is safe to call twice


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is safe to call twice")
var t = HostDebugTarget.launch(FIXTURE)
assert_equal(t.detach(), "")
assert_equal(t.detach(), "")
```

</details>

#### stops stepping once detached

- stops stepping once detached


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops stepping once detached")
var t = HostDebugTarget.launch(FIXTURE)
t.detach()
val s = t.step()
assert_equal(s.pc, 4)
assert_equal(s.stop_reason, "halt")
```

</details>

#### stops resuming once detached

- stops resuming once detached


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops resuming once detached")
var t = HostDebugTarget.launch(FIXTURE)
t.detach()
val s = t.resume()
assert_equal(s.stop_reason, "halt")
```

</details>

#### refuses new breakpoints once detached

- refuses new breakpoints once detached


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses new breakpoints once detached")
var t = HostDebugTarget.launch(FIXTURE)
t.detach()
assert_false(t.set_breakpoint(6))
```

</details>

#### reads no memory once detached

- reads no memory once detached


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads no memory once detached")
var t = HostDebugTarget.launch(FIXTURE)
t.detach()
assert_equal(t.read_mem(0, 4).len(), 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/dap/host_debug_target_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HostDebugTarget identity, HostDebugTarget state, HostDebugTarget breakpoints, HostDebugTarget step, HostDebugTarget resume, HostDebugTarget read_mem, HostDebugTarget detach.
- HostDebugTarget identity
- HostDebugTarget state
- HostDebugTarget breakpoints
- HostDebugTarget step
- HostDebugTarget resume
- HostDebugTarget read_mem
- HostDebugTarget detach

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
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

- Canonical SPipe generation for source `3bc4851f883c4ef47f606b4a0934bb96907ded2faea740a14cdd30c3a48c19b4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3bc4851f883c4ef47f606b4a0934bb96907ded2faea740a14cdd30c3a48c19b4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3bc4851f883c4ef47f606b4a0934bb96907ded2faea740a14cdd30c3a48c19b4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/dap/host_debug_target_spec.spl
mirror: doc/06_spec/01_unit/app/dap/host_debug_target_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/dap/host_debug_target_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/dap/host_debug_target_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/dap/host_debug_target_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports the host kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/dap/host_debug_target_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports Native debug capability' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/dap/host_debug_target_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts on the first executable line with line pc units' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
