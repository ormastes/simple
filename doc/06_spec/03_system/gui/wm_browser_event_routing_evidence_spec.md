# Wm Browser Event Routing Evidence Specification

> Tests covering WM browser event routing evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Browser Event Routing Evidence Specification

## Scenarios

### WM browser event routing evidence

#### blocks diagnostic launch flags instead of treating them as production proof

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- blocks diagnostic launch flags instead of treating them as production proof


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("blocks diagnostic launch flags instead of treating them as production proof")
val run_id = _run_id()
val build_dir = "build/tmp/wm_browser_event_routing_diagnostic_spec_" + run_id
val cmd = "BUILD_DIR=" + build_dir + " REPORT_PATH=" + build_dir + "/report.md" +
    " WM_BROWSER_EVENT_ROUTING_DIAGNOSTIC_FLAGS=--disable-gpu" +
    " sh scripts/check/check-wm-browser-event-routing-evidence.shs"
val result = process_run_timeout("/bin/sh", ["-c", cmd], 5000)
expect(result[2]).to_be_greater_than(0)
expect(result[0]).to_contain("wm_browser_event_routing_status=blocked")
expect(result[0]).to_contain("wm_browser_event_routing_reason=diagnostic-launch-flags-not-production")
expect(result[0]).to_contain("wm_browser_event_routing_renderer_sandboxed=unavailable")
expect(result[0]).to_contain("wm_browser_event_routing_gpu_compositing_status=unavailable")
expect(result[0]).to_contain("wm_browser_event_routing_webgl_status=unavailable")
```

</details>

#### fails closed when a valid Simple run ID has no Aetheric production proof

- fails closed when a valid Simple run ID has no Aetheric production proof
- Provide a valid caller-supplied Simple run ID
- Reject the missing canonical Aetheric production proof before Electron


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails closed when a valid Simple run ID has no Aetheric production proof")
step("Provide a valid caller-supplied Simple run ID")
val run_id = _run_id()
val result = _run_checker(run_id)

step("Reject the missing canonical Aetheric production proof before Electron")
expect(result[2]).to_be_greater_than(0)
expect(result[0]).to_contain("wm_browser_event_routing_status=fail")
expect(result[0]).to_contain("wm_browser_event_routing_reason=missing-aetheric-production-proof")

val report = file_read_text(_report_path(run_id)) ?? ""
expect(report).to_contain("- status: fail")
expect(report).to_contain("- reason: missing-aetheric-production-proof")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/wm_browser_event_routing_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WM browser event routing evidence.
- WM browser event routing evidence

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `20c44e8155dfac0ed0367d7b3d45de884ccd512b129e029bbaf645567f0240e2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `20c44e8155dfac0ed0367d7b3d45de884ccd512b129e029bbaf645567f0240e2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `20c44e8155dfac0ed0367d7b3d45de884ccd512b129e029bbaf645567f0240e2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/gui/wm_browser_event_routing_evidence_spec.spl
mirror: doc/06_spec/03_system/gui/wm_browser_event_routing_evidence_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gui/wm_browser_event_routing_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gui/wm_browser_event_routing_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gui/wm_browser_event_routing_evidence_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'blocks diagnostic launch flags instead of treating them as production proof' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gui/wm_browser_event_routing_evidence_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed when a valid Simple run ID has no Aetheric production proof' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
