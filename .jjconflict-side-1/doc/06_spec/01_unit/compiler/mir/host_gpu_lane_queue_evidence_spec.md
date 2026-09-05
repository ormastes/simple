# Host Gpu Lane Queue Evidence Specification

> Tests covering Host/GPU lane MIR queue evidence.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Gpu Lane Queue Evidence Specification

## Scenarios

### Host/GPU lane MIR queue evidence

#### turns lowered MIR lane markers into strict queue submission evidence

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- turns lowered MIR lane markers into strict queue submission evidence
   - Expected: host_gpu_mir_submission_score(src, "f", true, 1113616374) equals `11111`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("turns lowered MIR lane markers into strict queue submission evidence")
val src = "fn f():\n    target.later(max_packet: 512) gpu \\:\n        val draw_ir_batch = \"batch\"\n"
expect(host_gpu_mir_submission_score(src, "f", true, 1113616374)).to_equal(11111)
```

</details>

#### rejects fallback MIR lane packets before device submission

- rejects fallback MIR lane packets before device submission
   - Expected: host_gpu_mir_submission_score(src, "f", false, 1113616374) equals `100111`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("rejects fallback MIR lane packets before device submission")
val src = "fn f():\n    target.later(max_packet: 512) gpu \\:\n        val draw_ir_batch = \"batch\"\n"
expect(host_gpu_mir_submission_score(src, "f", false, 1113616374)).to_equal(100111)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/host_gpu_lane_queue_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Host/GPU lane MIR queue evidence.
- Host/GPU lane MIR queue evidence

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6a3b75e8cf30cd16727012ce3c47ef789b2d739cdcd550485e772e5417b407b6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6a3b75e8cf30cd16727012ce3c47ef789b2d739cdcd550485e772e5417b407b6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6a3b75e8cf30cd16727012ce3c47ef789b2d739cdcd550485e772e5417b407b6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/mir/host_gpu_lane_queue_evidence_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/host_gpu_lane_queue_evidence_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/host_gpu_lane_queue_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/host_gpu_lane_queue_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/host_gpu_lane_queue_evidence_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/mir/host_gpu_lane_queue_evidence_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'turns lowered MIR lane markers into strict queue submission evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/host_gpu_lane_queue_evidence_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects fallback MIR lane packets before device submission' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
