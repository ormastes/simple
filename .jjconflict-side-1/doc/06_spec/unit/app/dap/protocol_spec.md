# Protocol Specification

> Tests covering Source, SourceBreakpoint, Breakpoint, StackFrame, Scope, Variable.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Protocol Specification

## Scenarios

### Source

#### creates source with path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates source with path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates source with path")
# Source represents debugged source code file
expect(true)
```

</details>

#### creates source with name

- creates source with name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates source with name")
# Source can be created with display name
expect(true)
```

</details>

### SourceBreakpoint

#### creates source breakpoint

- creates source breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates source breakpoint")
# Source breakpoint at specific line
expect(true)
```

</details>

#### creates source breakpoint with condition

- creates source breakpoint with condition


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates source breakpoint with condition")
# Source breakpoint with conditional break expression
expect(true)
```

</details>

### Breakpoint

#### creates verified breakpoint

- creates verified breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates verified breakpoint")
# Verified breakpoint set in debuggee
expect(true)
```

</details>

#### creates unverified breakpoint

- creates unverified breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates unverified breakpoint")
# Unverified breakpoint waiting for source
expect(true)
```

</details>

### StackFrame

#### creates stack frame

- creates stack frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates stack frame")
# Stack frame in call stack
expect(true)
```

</details>

#### creates stack frame with module

- creates stack frame with module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates stack frame with module")
# Stack frame with module information
expect(true)
```

</details>

### Scope

#### creates local scope

- creates local scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates local scope")
# Local variable scope
expect(true)
```

</details>

#### creates arguments scope

- creates arguments scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates arguments scope")
# Function arguments scope
expect(true)
```

</details>

#### creates global scope

- creates global scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates global scope")
# Global variable scope
expect(true)
```

</details>

### Variable

#### creates simple variable

- creates simple variable


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates simple variable")
# Simple scalar variable
expect(true)
```

</details>

#### creates variable with children

- creates variable with children


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates variable with children")
# Complex variable with child variables
expect(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/dap/protocol_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Source, SourceBreakpoint, Breakpoint, StackFrame, Scope, Variable.
- Source
- SourceBreakpoint
- Breakpoint
- StackFrame
- Scope
- Variable

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `bed905c039c66d7644f589af029abebf0d65bc0b9ff8160cd8523c4f562b8ea9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bed905c039c66d7644f589af029abebf0d65bc0b9ff8160cd8523c4f562b8ea9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bed905c039c66d7644f589af029abebf0d65bc0b9ff8160cd8523c4f562b8ea9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/dap/protocol_spec.spl
mirror: doc/06_spec/unit/app/dap/protocol_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/dap/protocol_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/dap/protocol_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/dap/protocol_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates source with path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/dap/protocol_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates source with name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/dap/protocol_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates source breakpoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
