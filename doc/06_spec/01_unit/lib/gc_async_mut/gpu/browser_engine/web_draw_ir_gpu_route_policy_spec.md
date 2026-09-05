# Web Draw Ir Gpu Route Policy Specification

> Tests covering Draw IR GPU route policy receipts.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Draw Ir Gpu Route Policy Specification

## Scenarios

### Draw IR GPU route policy receipts

#### reset and copied evidence defaults

#### starts unavailable without consulting a renderer

- starts unavailable without consulting a renderer
   - Expected: web_draw_ir_gpu_route_policy_consult_count() equals `0`
   - Expected: evidence.backend_name equals ``
   - Expected: evidence.available is false
   - Expected: evidence.sample_count equals `0`
   - Expected: evidence.should_offload is false
   - Expected: evidence.reason equals `timing-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("starts unavailable without consulting a renderer")
web_draw_ir_gpu_route_policy_reset()
val evidence = web_draw_ir_gpu_route_last_evidence()
expect(web_draw_ir_gpu_route_policy_consult_count()).to_equal(0)
expect(evidence.backend_name).to_equal("")
expect(evidence.available).to_equal(false)
expect(evidence.sample_count).to_equal(0)
expect(evidence.should_offload).to_equal(false)
expect(evidence.reason).to_equal("timing-unavailable")
```

</details>

#### returns a value copy rather than a mutable cache object

- returns a value copy rather than a mutable cache object
   - Expected: second.backend_name equals ``
   - Expected: second.reason equals `timing-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns a value copy rather than a mutable cache object")
web_draw_ir_gpu_route_policy_reset()
val first = web_draw_ir_gpu_route_last_evidence()
first.backend_name = "changed"
val second = web_draw_ir_gpu_route_last_evidence()
expect(second.backend_name).to_equal("")
expect(second.reason).to_equal("timing-unavailable")
```

</details>

#### pure measured evidence

#### requires three paired samples and a strict 100us margin

- requires three paired samples and a strict 100us margin
   - Expected: pending.available is false
   - Expected: pending.reason equals `timing-unavailable`
   - Expected: tie.available is true
   - Expected: tie.should_offload is false
   - Expected: winner.available is true
   - Expected: winner.should_offload is true
   - Expected: winner.reason equals `measured-gpu-faster`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires three paired samples and a strict 100us margin")
val pending = web_gpu_paint_timing_evidence(
    "vulkan", 900, 1000, 600, 700, 2, true, true, true)
val tie = web_gpu_paint_timing_evidence(
    "vulkan", 900, 1000, 600, 900, 3, true, true, true)
val winner = web_gpu_paint_timing_evidence(
    "vulkan", 900, 1000, 600, 800, 3, true, true, true)
expect(pending.available).to_equal(false)
expect(pending.reason).to_equal("timing-unavailable")
expect(tie.available).to_equal(true)
expect(tie.should_offload).to_equal(false)
expect(winner.available).to_equal(true)
expect(winner.should_offload).to_equal(true)
expect(winner.reason).to_equal("measured-gpu-faster")
```

</details>

#### fails closed on parity or device provenance failure

- fails closed on parity or device provenance failure
   - Expected: mismatch.available is false
   - Expected: mismatch.should_offload is false
   - Expected: mismatch.reason equals `pixel-mismatch`
   - Expected: unproven.available is false
   - Expected: unproven.should_offload is false
   - Expected: unproven.reason equals `device-proof-unavailable`
   - Expected: skipped.available is false
   - Expected: skipped.pixels_match is true
   - Expected: skipped.commands_complete is false
   - Expected: skipped.reason equals `commands-skipped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed on parity or device provenance failure")
val mismatch = web_gpu_paint_timing_evidence(
    "cuda", 900, 1000, 600, 700, 3, false, true, true)
val unproven = web_gpu_paint_timing_evidence(
    "metal", 900, 1000, 600, 700, 3, true, true, false)
val skipped = web_gpu_paint_timing_evidence(
    "vulkan", 900, 1000, 600, 700, 3, true, true, true, false)
expect(mismatch.available).to_equal(false)
expect(mismatch.should_offload).to_equal(false)
expect(mismatch.reason).to_equal("pixel-mismatch")
expect(unproven.available).to_equal(false)
expect(unproven.should_offload).to_equal(false)
expect(unproven.reason).to_equal("device-proof-unavailable")
expect(skipped.available).to_equal(false)
expect(skipped.pixels_match).to_equal(true)
expect(skipped.commands_complete).to_equal(false)
expect(skipped.reason).to_equal("commands-skipped")
```

</details>

#### completed route recovery

#### evicts failed device evidence so the next frame recalibrates

- evicts failed device evidence so the next frame recalibrates
- sample a composition against a backend with no live device
- the failed route leaves no stale success evidence
   - Expected: pixels.len() equals `64 * 64`
   - Expected: failed.available is false
   - Expected: failed.should_offload is false
- the next consult recalibrates from scratch rather than reusing the failed state
   - Expected: web_draw_ir_gpu_route_policy_consult_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("evicts failed device evidence so the next frame recalibrates")
step("sample a composition against a backend with no live device")
web_draw_ir_gpu_route_policy_reset()
val embedding = draw_ir_embedding_config(
    "web", "body", 0, 0, 64, 64, 0, 1000, true)
val composition = draw_ir_composition(
    "web-gpu-route-policy", "generic-web", "gpu", [
        draw_ir_batch("body", "gpu", embedding, [
            draw_ir_rect("background", 0, 0, 64, 64, 0xFF1D4ED8u32)
        ])
    ])
val pixels = web_draw_ir_gpu_route_sample(composition, 64, 64, "no-such-backend")
step("the failed route leaves no stale success evidence")
# oracle: a device-less backend must still render correctly via the
# software fallback and record failure, never a stale success receipt
expect(pixels.len()).to_equal(64 * 64)
val failed = web_draw_ir_gpu_route_last_evidence()
expect(failed.available).to_equal(false)
expect(failed.should_offload).to_equal(false)
step("the next consult recalibrates from scratch rather than reusing the failed state")
web_draw_ir_gpu_route_sample(composition, 64, 64, "no-such-backend")
# oracle: consult count advances — each frame re-consults after eviction
expect(web_draw_ir_gpu_route_policy_consult_count()).to_equal(2)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_draw_ir_gpu_route_policy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Draw IR GPU route policy receipts.
- Draw IR GPU route policy receipts

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bf96524527e2aa7a2c19e4bbddb06a95878d377e7b090bc837259516f4ca0594`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bf96524527e2aa7a2c19e4bbddb06a95878d377e7b090bc837259516f4ca0594`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bf96524527e2aa7a2c19e4bbddb06a95878d377e7b090bc837259516f4ca0594`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_draw_ir_gpu_route_policy_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_draw_ir_gpu_route_policy_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_draw_ir_gpu_route_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_draw_ir_gpu_route_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_draw_ir_gpu_route_policy_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
