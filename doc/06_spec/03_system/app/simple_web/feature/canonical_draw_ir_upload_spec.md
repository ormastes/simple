# canonical_draw_ir_upload_spec

> Canonical Simple Web Draw IR upload routing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# canonical_draw_ir_upload_spec

Canonical Simple Web Draw IR upload routing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_web/feature/canonical_draw_ir_upload_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Canonical Simple Web Draw IR upload routing.

The upload-bound route must execute the exact WebIR-produced
`DrawIrComposition` through Engine2D. It must not reconstruct pixels through a
browser-private painter before selecting the Engine2D frame.

## Scenarios

### Simple Web canonical Draw IR upload

#### should submit the WebIR composition once per measured Engine2D lane

- should submit the WebIR composition once per measured Engine2D lane
   - GUI capture: after_step (HTML preferred when available)
- Build one canonical web composition
   - GUI capture: after_step (HTML preferred when available)
- Submit it through the upload route
   - GUI capture: after_step (HTML preferred when available)
- Read back the selected Engine2D frame
   - GUI capture: after_step (HTML preferred when available)
- Match structured Draw IR and exact pixels
   - GUI capture: after_step (HTML preferred when available)


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should submit the WebIR composition once per measured Engine2D lane")
step("Build one canonical web composition")
val composition = setup_canonical_upload_fixture()

step("Submit it through the upload route")
val pixels = check_same_composition_submitted(composition)

step("Read back the selected Engine2D frame")
check_backend_receipt_selected()

step("Match structured Draw IR and exact pixels")
check_upload_pixels_exact(pixels)
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7a3c7fa0ea4ea8c6bb5aa34b858df717c95ebfc1e7677aeef172cbecca06c662`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7a3c7fa0ea4ea8c6bb5aa34b858df717c95ebfc1e7677aeef172cbecca06c662`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7a3c7fa0ea4ea8c6bb5aa34b858df717c95ebfc1e7677aeef172cbecca06c662`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/03_system/app/simple_web/feature/canonical_draw_ir_upload_spec.spl
mirror: doc/06_spec/03_system/app/simple_web/feature/canonical_draw_ir_upload_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simple_web/feature/canonical_draw_ir_upload_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_web/feature/canonical_draw_ir_upload_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_web/feature/canonical_draw_ir_upload_spec.spl:112:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should submit the WebIR composition once per measured Engine2D lane' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_web/feature/canonical_draw_ir_upload_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should submit the WebIR composition once per measured Engine2D lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
