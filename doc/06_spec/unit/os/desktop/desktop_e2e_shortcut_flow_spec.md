# Desktop E2e Shortcut Flow Specification

> Tests covering desktop e2e shortcut flow.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Desktop E2e Shortcut Flow Specification

## Scenarios

### desktop e2e shortcut flow

#### does not return before SYS-GUI-002 shortcut and wm markers on no-vfs boots

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- does not return before SYS-GUI-002 shortcut and wm markers on no-vfs boots
   - Expected: source does not contain `old_cutoff`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not return before SYS-GUI-002 shortcut and wm markers on no-vfs boots")
val source = rt_file_read_text(DESKTOP_E2E_ENTRY)
val skip_idx = source.find("[desktop-e2e] storage-backed-launch:skip reason=no-vfs")
val shortcut_idx = source.find("[desktop-e2e] shortcut dispatch begin")
val wm_idx = source.find("[desktop-e2e] wm:ok pid=")
val old_cutoff = "storage-backed-launch:skip reason=no-vfs\")\n        return true"

expect(skip_idx).to_be_greater_than(0)
expect(shortcut_idx).to_be_greater_than(skip_idx)
expect(wm_idx).to_be_greater_than(shortcut_idx)
expect(source.contains(old_cutoff)).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/desktop/desktop_e2e_shortcut_flow_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering desktop e2e shortcut flow.
- desktop e2e shortcut flow

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

- Canonical SPipe generation for source `9c654dd652c64ddf56f9095da2ad5404421f5ac8d4eff0746546a6fe4b322914`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c654dd652c64ddf56f9095da2ad5404421f5ac8d4eff0746546a6fe4b322914`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c654dd652c64ddf56f9095da2ad5404421f5ac8d4eff0746546a6fe4b322914`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/os/desktop/desktop_e2e_shortcut_flow_spec.spl
mirror: doc/06_spec/unit/os/desktop/desktop_e2e_shortcut_flow_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=85; blocker cap makes effective=49
doc/06_spec/unit/os/desktop/desktop_e2e_shortcut_flow_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/desktop/desktop_e2e_shortcut_flow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/desktop/desktop_e2e_shortcut_flow_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/unit/os/desktop/desktop_e2e_shortcut_flow_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not return before SYS-GUI-002 shortcut and wm markers on no-vfs boots' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
