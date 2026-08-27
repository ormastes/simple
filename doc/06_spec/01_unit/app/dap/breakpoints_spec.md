# Breakpoints Specification

> Tests covering BreakpointEntry, BreakpointManager.

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

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates breakpoint entry")
val breakpoints = rt_file_read_text("src/lib/nogc_sync_mut/dap/breakpoints.spl")
expect(breakpoints).to_contain("fn new(id: Int, source_path: String, line: Int) -> BreakpointEntry:")
expect(breakpoints).to_contain("verified: true,  # For now, always verify")
```

</details>

#### adds condition to breakpoint

- adds condition to breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds condition to breakpoint")
val breakpoints = rt_file_read_text("src/lib/nogc_sync_mut/dap/breakpoints.spl")
expect(breakpoints).to_contain("fn with_condition(condition: String) -> BreakpointEntry:")
expect(breakpoints).to_contain("condition: Some(condition),")
```

</details>

#### adds hit condition to breakpoint

- adds hit condition to breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds hit condition to breakpoint")
# KNOWN GAP: BreakpointEntry has a hit_condition field, but unlike
# with_condition() there is no with_hit_condition() builder, and
# BreakpointManager.set_breakpoints() never populates hit_condition
# from the incoming SourceBreakpoint at all. Asserting the described
# behaviour honestly so this fails until a builder is added.
# See doc/08_tracking/bug/dap_spec_stubs_reported_green_without_asserting_2026-08-08.md
val breakpoints = rt_file_read_text("src/lib/nogc_sync_mut/dap/breakpoints.spl")
expect(breakpoints).to_contain("fn with_hit_condition(hit_condition: String) -> BreakpointEntry:")
```

</details>

#### increments hit count

- increments hit count


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("increments hit count")
val breakpoints = rt_file_read_text("src/lib/nogc_sync_mut/dap/breakpoints.spl")
expect(breakpoints).to_contain("fn increment_hit_count(breakpoint_id: Int):")
expect(breakpoints).to_contain("bp.hit_count = bp.hit_count + 1")
```

</details>

### BreakpointManager

#### adds breakpoints

- adds breakpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds breakpoints")
val breakpoints = rt_file_read_text("src/lib/nogc_sync_mut/dap/breakpoints.spl")
expect(breakpoints).to_contain("fn set_breakpoints(source_path: String, source_breakpoints: [protocol.SourceBreakpoint]) -> [BreakpointEntry]:")
expect(breakpoints).to_contain("entries.push(entry)")
expect(breakpoints).to_contain("self.breakpoints[source_path] = entries")
```

</details>

#### removes breakpoints (setBreakpoints replaces the prior set for a source)

- removes breakpoints (setBreakpoints replaces the prior set for a source)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes breakpoints (setBreakpoints replaces the prior set for a source)")
# DAP's setBreakpoints request is idempotent-replace, not incremental
# add/remove: set_breakpoints() clears the source's existing entries
# before installing the new list, so calling it with an empty list
# removes all breakpoints previously set for that source.
val breakpoints = rt_file_read_text("src/lib/nogc_sync_mut/dap/breakpoints.spl")
expect(breakpoints).to_contain("self.breakpoints.remove(source_path)")
```

</details>

#### finds breakpoints by location

- finds breakpoints by location


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds breakpoints by location")
val breakpoints = rt_file_read_text("src/lib/nogc_sync_mut/dap/breakpoints.spl")
expect(breakpoints).to_contain("fn should_stop_at_line(source_path: String, line: Int) -> Option<BreakpointEntry>:")
expect(breakpoints).to_contain("if bp.line == line:")
```

</details>

#### generates unique IDs

- generates unique IDs


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates unique IDs")
val breakpoints = rt_file_read_text("src/lib/nogc_sync_mut/dap/breakpoints.spl")
expect(breakpoints).to_contain("val id = self.next_id")
expect(breakpoints).to_contain("self.next_id = self.next_id + 1")
```

</details>

#### clears all breakpoints

- clears all breakpoints


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears all breakpoints")
# KNOWN GAP: clear_breakpoints(source_path) only clears the entries
# for ONE source path -- there is no method that clears every
# breakpoint across all sources in the manager. Asserting the
# described "clears all" behaviour honestly so this fails until such
# a method exists.
# See doc/08_tracking/bug/dap_spec_stubs_reported_green_without_asserting_2026-08-08.md
val breakpoints = rt_file_read_text("src/lib/nogc_sync_mut/dap/breakpoints.spl")
expect(breakpoints).to_contain("fn clear_all_breakpoints() -> Nil:")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/dap/breakpoints_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering BreakpointEntry, BreakpointManager.
- BreakpointEntry
- BreakpointManager

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

- Canonical SPipe generation for source `6413bbfef57b94a755b59e6d0bf720b494c3db8665c2aaa3e60ceca4f8e7bca1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6413bbfef57b94a755b59e6d0bf720b494c3db8665c2aaa3e60ceca4f8e7bca1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6413bbfef57b94a755b59e6d0bf720b494c3db8665c2aaa3e60ceca4f8e7bca1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/dap/breakpoints_spec.spl
mirror: doc/06_spec/01_unit/app/dap/breakpoints_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/dap/breakpoints_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/dap/breakpoints_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/dap/breakpoints_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates breakpoint entry' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/dap/breakpoints_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds condition to breakpoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/dap/breakpoints_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds hit condition to breakpoint' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
