# Tmux Facade Specification

> Tests covering gc_async_mut tmux facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tmux Facade Specification

## Scenarios

### gc_async_mut tmux facade

#### re-exports tmux record types without invoking shell-backed tmux operations

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports tmux record types without invoking shell-backed tmux operations
   - Expected: session.name equals `dev`
   - Expected: session.windows equals `2`
   - Expected: session.attached is true
   - Expected: window.session equals `dev`
   - Expected: window.index equals `1`
   - Expected: window.panes equals `3`
   - Expected: pane.active is true
   - Expected: pane.width equals `120`
   - Expected: pane.current_command equals `bash`
   - Expected: capture.content equals `output`
   - Expected: capture.pane_id equals `dev:1.2`
   - Expected: capture.rows equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports tmux record types without invoking shell-backed tmux operations")
val session = TmuxSession(name: "dev", windows: 2, attached: true, created: "now")
expect(session.name).to_equal("dev")
expect(session.windows).to_equal(2)
expect(session.attached).to_equal(true)

val window = TmuxWindow(session: "dev", index: 1, name: "edit", active: false, panes: 3)
expect(window.session).to_equal("dev")
expect(window.index).to_equal(1)
expect(window.panes).to_equal(3)

val pane = TmuxPane(session: "dev", window_index: 1, pane_index: 2, active: true, width: 120, height: 40, current_command: "bash", pid: 42)
expect(pane.active).to_equal(true)
expect(pane.width).to_equal(120)
expect(pane.current_command).to_equal("bash")

val capture = TmuxCaptureResult(content: "output", pane_id: "dev:1.2", rows: 40)
expect(capture.content).to_equal("output")
expect(capture.pane_id).to_equal("dev:1.2")
expect(capture.rows).to_equal(40)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/tmux/tmux_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering gc_async_mut tmux facade.
- gc_async_mut tmux facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `c75c62cb6b16b1b60595464c5c5982088bfd627cd033e0f715cf22ff5c80ffb9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c75c62cb6b16b1b60595464c5c5982088bfd627cd033e0f715cf22ff5c80ffb9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c75c62cb6b16b1b60595464c5c5982088bfd627cd033e0f715cf22ff5c80ffb9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/gc_async_mut/tmux/tmux_facade_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/tmux/tmux_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/tmux/tmux_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/tmux/tmux_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/tmux/tmux_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 5 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/tmux/tmux_facade_spec.spl:13:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports tmux record types without invoking shell-backed tmux operations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
