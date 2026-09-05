# Web Draw Ir Gpu Route Device Measured Specification

> Tests covering Primary web Draw IR measured device route.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Draw Ir Gpu Route Device Measured Specification

## Scenarios

### Primary web Draw IR measured device route

#### calibrates one pair per composition with exact device parity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- calibrates one pair per composition with exact device parity
   - Expected: evidence.sample_count equals `sample`
   - Expected: pixels equals `oracle`
   - Expected: web_draw_ir_gpu_route_policy_consult_count() equals `3`
   - Expected: measured.available is true
   - Expected: measured.pixels_match is true
   - Expected: measured.upload_device_proven is true
   - Expected: measured.gpu_device_proven is true
   - Expected: reused equals `oracle`
   - Expected: web_draw_ir_gpu_route_last_evidence().sample_count equals `3`
   - Expected: web_draw_ir_gpu_route_policy_consult_count() equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("calibrates one pair per composition with exact device parity")
web_draw_ir_gpu_route_policy_reset()
val embedding = draw_ir_embedding_config(
    "web", "body", 0, 0, 64, 64, 0, 1000, true)
val composition = draw_ir_composition(
    "web-gpu-route", "generic-web", "gpu", [
        draw_ir_batch("body", "gpu", embedding, [
            draw_ir_rect("background", 0, 0, 64, 64, 0xFF1D4ED8u32)
        ])
    ])
val oracle = simple_web_render_draw_ir_composition_with_cpu_backend(
    composition, 64, 64)
var sample = 1
while sample <= 3:
    val pixels = web_draw_ir_gpu_route_sample(
        composition, 64, 64, measured_backend())
    val evidence = web_draw_ir_gpu_route_last_evidence()
    expect(evidence.sample_count).to_equal(sample)
    expect(pixels).to_equal(oracle)
    sample = sample + 1
val measured = web_draw_ir_gpu_route_last_evidence()
expect(web_draw_ir_gpu_route_policy_consult_count()).to_equal(3)
expect(measured.available).to_equal(true)
expect(measured.pixels_match).to_equal(true)
expect(measured.upload_device_proven).to_equal(true)
expect(measured.gpu_device_proven).to_equal(true)
expect(
    measured.reason == "measured-gpu-faster" or
    measured.reason == "measured-gpu-slower-overhead"
).to_equal(true)
val reused = web_draw_ir_gpu_route_sample(
    composition, 64, 64, measured_backend())
expect(reused).to_equal(oracle)
expect(web_draw_ir_gpu_route_last_evidence().sample_count).to_equal(3)
expect(web_draw_ir_gpu_route_policy_consult_count()).to_equal(4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/web_render_chrome/web_draw_ir_gpu_route_device_measured_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Primary web Draw IR measured device route.
- Primary web Draw IR measured device route

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

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `94943592a57f06bd867aa418d65ea0583c477656ed11f2017b0a2cf7878310b8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `94943592a57f06bd867aa418d65ea0583c477656ed11f2017b0a2cf7878310b8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `94943592a57f06bd867aa418d65ea0583c477656ed11f2017b0a2cf7878310b8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/05_perf/web_render_chrome/web_draw_ir_gpu_route_device_measured_spec.spl
mirror: doc/06_spec/05_perf/web_render_chrome/web_draw_ir_gpu_route_device_measured_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/web_render_chrome/web_draw_ir_gpu_route_device_measured_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/web_render_chrome/web_draw_ir_gpu_route_device_measured_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/web_render_chrome/web_draw_ir_gpu_route_device_measured_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
