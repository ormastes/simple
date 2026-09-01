# Phase3 Session Closure Guard Specification

> Tests covering Phase 3 Office UI session closure.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Phase3 Session Closure Guard Specification

## Scenarios

### Phase 3 Office UI session closure

#### keeps SQLite outside the core UISession module

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps SQLite outside the core UISession module


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps SQLite outside the core UISession module")
val source = rt_file_read_text("src/lib/nogc_sync_mut/ui/session.spl") ?? ""
expect(source.contains("ui.access_store")).to_be(false)
expect(source.contains("database.sql")).to_be(false)
expect(source).to_contain("UiAccessPersistence")
```

</details>

#### uses the shared monotonic time owner in the UI test handler

- uses the shared monotonic time owner in the UI test handler


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("uses the shared monotonic time owner in the UI test handler")
val source = rt_file_read_text("src/app/ui.test_api/handler.spl") ?? ""
expect(source.contains("extern fn rt_time_ms")).to_be(false)
expect(source).to_contain("time_now_micros")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/phase3_session_closure_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Phase 3 Office UI session closure.
- Phase 3 Office UI session closure

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0ce132caacd92b5ec07d3910357b8d8e7f9707483ab60af05931af637dc4c147`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0ce132caacd92b5ec07d3910357b8d8e7f9707483ab60af05931af637dc4c147`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0ce132caacd92b5ec07d3910357b8d8e7f9707483ab60af05931af637dc4c147`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **78/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/app/ui/phase3_session_closure_guard_spec.spl
mirror: doc/06_spec/01_unit/app/ui/phase3_session_closure_guard_spec.md (current)
findings: 6 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=78; blocker cap makes effective=49
doc/06_spec/01_unit/app/ui/phase3_session_closure_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui/phase3_session_closure_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui/phase3_session_closure_guard_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/app/ui/phase3_session_closure_guard_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/ui/phase3_session_closure_guard_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps SQLite outside the core UISession module' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/phase3_session_closure_guard_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the shared monotonic time owner in the UI test handler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
