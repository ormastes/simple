# Wine Seh Frame Specification

> Tests covering Wine SEH frame-chain planner.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wine Seh Frame Specification

## Scenarios

### Wine SEH frame-chain planner

#### plans SEH dispatch when a thread frame and mapped handler exist

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- plans SEH dispatch when a thread frame and mapped handler exist
   - Expected: result.ok is true
   - Expected: result.status equals `seh-dispatch-planned`
   - Expected: result.handler_address equals `0x403000`
   - Expected: result.frame_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("plans SEH dispatch when a thread frame and mapped handler exist")
val fault = WineVmFault(process_id: 77, thread_id: 12, address: 0x402000, access: "execute", policy: "deliver-seh")
val frame = wine_seh_frame_new(77, 12, 0x701000, 0x403000, 0x700000, 0x710000)
val result = wine_seh_dispatch_fault(fault, [frame], 0x400000, 0x5000)
expect(result.ok).to_equal(true)
expect(result.status).to_equal("seh-dispatch-planned")
expect(result.handler_address).to_equal(0x403000)
expect(result.frame_count).to_equal(1)
expect(result.evidence).to_contain("seh-frame-chain-present")
expect(result.evidence).to_contain("seh-handler-mapped")
expect(result.evidence).to_contain("no-seh-handler-executed")
```

</details>

#### rejects frame handlers outside the mapped image

- rejects frame handlers outside the mapped image
   - Expected: result.ok is false
   - Expected: result.error equals `seh-handler-unmapped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects frame handlers outside the mapped image")
val fault = WineVmFault(process_id: 77, thread_id: 12, address: 0x402000, access: "execute", policy: "deliver-seh")
val frame = wine_seh_frame_new(77, 12, 0x701000, 0x500000, 0x700000, 0x710000)
val result = wine_seh_dispatch_fault(fault, [frame], 0x400000, 0x5000)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("seh-handler-unmapped")
expect(result.evidence).to_contain("seh-dispatch-blocked")
```

</details>

#### rejects non-SEH fault policies before handler handoff

- rejects non-SEH fault policies before handler handoff
   - Expected: result.ok is false
   - Expected: result.error equals `seh-policy:terminate-process`
   - Expected: result.frame_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects non-SEH fault policies before handler handoff")
val fault = WineVmFault(process_id: 77, thread_id: 12, address: 0x402000, access: "execute", policy: "terminate-process")
val frame = wine_seh_frame_new(77, 12, 0x701000, 0x403000, 0x700000, 0x710000)
val result = wine_seh_dispatch_fault(fault, [frame], 0x400000, 0x5000)
expect(result.ok).to_equal(false)
expect(result.error).to_equal("seh-policy:terminate-process")
expect(result.frame_count).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/wine_seh_frame_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Wine SEH frame-chain planner.
- Wine SEH frame-chain planner

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `5fe37796a0ff2e38c3d737f29cd34641bc2034cc5215a24e20f8309a90de571b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5fe37796a0ff2e38c3d737f29cd34641bc2034cc5215a24e20f8309a90de571b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5fe37796a0ff2e38c3d737f29cd34641bc2034cc5215a24e20f8309a90de571b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/wine_seh_frame_spec.spl
mirror: doc/06_spec/unit/lib/common/wine_seh_frame_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/wine_seh_frame_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/wine_seh_frame_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/wine_seh_frame_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/wine_seh_frame_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'plans SEH dispatch when a thread frame and mapped handler exist' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_seh_frame_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects frame handlers outside the mapped image' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/wine_seh_frame_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects non-SEH fault policies before handler handoff' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
