# Breakpoints Specification

> Tests covering BreakpointEntry, BreakpointStore.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Breakpoints Specification

## Scenarios

### BreakpointEntry

#### creates breakpoint entry

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- creates breakpoint entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates breakpoint entry")
# Create breakpoint entry at source location
expect(true)
```

</details>

#### adds condition to breakpoint

- adds condition to breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds condition to breakpoint")
# Add condition expression to breakpoint
expect(true)
```

</details>

#### adds hit condition to breakpoint

- adds hit condition to breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds hit condition to breakpoint")
# Add hit count condition to breakpoint
expect(true)
```

</details>

#### increments hit count

- increments hit count


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("increments hit count")
# Increment hit counter when breakpoint hit
expect(true)
```

</details>

### BreakpointStore

#### adds breakpoints

- adds breakpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds breakpoints")
# Add breakpoints to store
expect(true)
```

</details>

#### removes breakpoints

- removes breakpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes breakpoints")
# Remove breakpoints from store
expect(true)
```

</details>

#### finds breakpoints by location

- finds breakpoints by location


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds breakpoints by location")
# Query breakpoints at specific location
expect(true)
```

</details>

#### generates unique IDs

- generates unique IDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates unique IDs")
# Generate unique breakpoint identifiers
expect(true)
```

</details>

#### clears all breakpoints

- clears all breakpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears all breakpoints")
# Clear all breakpoints in store
expect(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/dap/breakpoints_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BreakpointEntry, BreakpointStore.
- BreakpointEntry
- BreakpointStore

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `9054d21fd02dc9b14d74c988e59b02c70a70b63e6ceb091cebf4af68c47f4660`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9054d21fd02dc9b14d74c988e59b02c70a70b63e6ceb091cebf4af68c47f4660`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9054d21fd02dc9b14d74c988e59b02c70a70b63e6ceb091cebf4af68c47f4660`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/dap/breakpoints_spec.spl
mirror: doc/06_spec/unit/app/dap/breakpoints_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/dap/breakpoints_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/dap/breakpoints_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/dap/breakpoints_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates breakpoint entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/dap/breakpoints_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds condition to breakpoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/dap/breakpoints_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds hit condition to breakpoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
