# Web Renderer GPU Paint Economics Specification

> Verifies the Simple Web GPU-paint cost model with deterministic `WebGpuPaintFrame` fixtures. The unit scenarios avoid the full HTML layout renderer so this spec stays a cheap guard for the CPU-work and communication overhead calculations. HTML-backed route coverage lives in the broader `web_gpu_paint_offload_matrix_spec`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Renderer GPU Paint Economics Specification

Verifies the Simple Web GPU-paint cost model with deterministic `WebGpuPaintFrame` fixtures. The unit scenarios avoid the full HTML layout renderer so this spec stays a cheap guard for the CPU-work and communication overhead calculations. HTML-backed route coverage lives in the broader `web_gpu_paint_offload_matrix_spec`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_gpu_paint_economics_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies the Simple Web GPU-paint cost model with deterministic
`WebGpuPaintFrame` fixtures. The unit scenarios avoid the full HTML layout
renderer so this spec stays a cheap guard for the CPU-work and communication
overhead calculations. HTML-backed route coverage lives in the broader
`web_gpu_paint_offload_matrix_spec`.

**Requirements:** N/A
**Plan:** N/A
**Design:** N/A
**Research:** N/A

## Examples

The scenarios cover transfer wins, total-work wins, CPU ground-truth frames
that must remain upload-bound, and frames with no GPU fill commands.

## Scenarios

### Simple web renderer GPU paint economics

#### backend policy

#### keeps cpu backends out of the gpu paint candidate set

- keeps cpu backends out of the gpu paint candidate set
   - Expected: web_gpu_paint_backend_verdict("cpu_simd") equals `cpu-backend-not-gpu-offload`
   - Expected: web_gpu_paint_backend_verdict("software") equals `cpu-backend-not-gpu-offload`
   - Expected: web_gpu_paint_backend_verdict("vulkan") equals `gpu-paint-candidate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps cpu backends out of the gpu paint candidate set")
expect(web_gpu_paint_backend_verdict("cpu_simd")).to_equal("cpu-backend-not-gpu-offload")
expect(web_gpu_paint_backend_verdict("software")).to_equal("cpu-backend-not-gpu-offload")
expect(web_gpu_paint_backend_verdict("vulkan")).to_equal("gpu-paint-candidate")
```

</details>

#### offload decision

#### offloads solid fills when transfer cost beats upload-bound presentation

- offloads solid fills when transfer cost beats upload-bound presentation
   - Expected: economics.cpu_paint_pixels equals `0`
   - Expected: economics.should_offload is true
   - Expected: economics.reason equals `gpu-paint-transfer-win`
   - Expected: economics.speed_verdict equals `estimated-gpu-faster`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("offloads solid fills when transfer cost beats upload-bound presentation")
val frame = solid_full_frame()
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.cpu_paint_pixels).to_equal(0)
expect(economics.fill_op_count).to_be_greater_than(0)
expect(economics.should_offload).to_equal(true)
expect(economics.reason).to_equal("gpu-paint-transfer-win")
expect(economics.speed_verdict).to_equal("estimated-gpu-faster")
expect(economics.gpu_paint_transfer_pixels).to_be_less_than(economics.upload_bound_transfer_pixels)
expect(economics.gpu_paint_total_pixels).to_be_less_than(economics.upload_bound_total_pixels)
```

</details>

#### offloads when skipped CPU paint beats command overhead overall

- offloads when skipped CPU paint beats command overhead overall
   - Expected: economics.should_offload is true
   - Expected: economics.reason equals `gpu-paint-total-win`
   - Expected: economics.speed_verdict equals `estimated-gpu-faster`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("offloads when skipped CPU paint beats command overhead overall")
val frame = many_tiny_fill_frame(0)
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.gpu_paint_transfer_pixels).to_be_greater_than(economics.upload_bound_transfer_pixels)
expect(economics.gpu_paint_total_pixels).to_be_less_than(economics.upload_bound_total_pixels)
expect(economics.should_offload).to_equal(true)
expect(economics.reason).to_equal("gpu-paint-total-win")
expect(economics.speed_verdict).to_equal("estimated-gpu-faster")
```

</details>

#### keeps CPU-ground-truth frames on the upload-bound path

- keeps CPU-ground-truth frames on the upload-bound path
   - Expected: economics.cpu_paint_pixels equals `16 * 16`
   - Expected: economics.should_offload is false
   - Expected: economics.reason equals `cpu-ground-truth-required`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps CPU-ground-truth frames on the upload-bound path")
val frame = cpu_ground_truth_frame()
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.cpu_paint_pixels).to_equal(16 * 16)
expect(economics.should_offload).to_equal(false)
expect(economics.reason).to_equal("cpu-ground-truth-required")
```

</details>

#### does not offload when there is no GPU fill work

- does not offload when there is no GPU fill work
   - Expected: economics.cpu_paint_pixels equals `0`
   - Expected: economics.should_offload is false
   - Expected: economics.reason equals `no-gpu-fill-ops`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not offload when there is no GPU fill work")
val frame = blank_frame()
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.cpu_paint_pixels).to_equal(0)
expect(economics.should_offload).to_equal(false)
expect(economics.reason).to_equal("no-gpu-fill-ops")
```

</details>

#### measured timing evidence

#### uses paired device-proven p95 timing to select GPU paint

- uses paired device-proven p95 timing to select GPU paint
   - Expected: timing.available is true
   - Expected: timing.should_offload is true
   - Expected: timing.reason equals `measured-gpu-faster`
   - Expected: timing.speed_verdict equals `measured-gpu-faster`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses paired device-proven p95 timing to select GPU paint")
val timing = web_gpu_paint_timing_evidence("cuda", 800, 1000, 400, 600, 3, true, true, true)
expect(timing.available).to_equal(true)
expect(timing.should_offload).to_equal(true)
expect(timing.reason).to_equal("measured-gpu-faster")
expect(timing.speed_verdict).to_equal("measured-gpu-faster")
```

</details>

#### keeps communication-bound GPU paint on the upload route

- keeps communication-bound GPU paint on the upload route
   - Expected: timing.available is true
   - Expected: timing.should_offload is false
   - Expected: timing.reason equals `measured-gpu-slower-overhead`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps communication-bound GPU paint on the upload route")
val timing = web_gpu_paint_timing_evidence("cuda", 40, 60, 80, 100, 3, true, true, true)
expect(timing.available).to_equal(true)
expect(timing.should_offload).to_equal(false)
expect(timing.reason).to_equal("measured-gpu-slower-overhead")
```

</details>

#### requires a strict margin above timing noise

- requires a strict margin above timing noise
   - Expected: boundary.available is true
   - Expected: boundary.should_offload is false
   - Expected: winner.should_offload is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("requires a strict margin above timing noise")
val boundary = web_gpu_paint_timing_evidence("cuda", 450, 500, 350, 400, 3, true, true, true)
val winner = web_gpu_paint_timing_evidence("cuda", 451, 501, 350, 400, 3, true, true, true)
expect(boundary.available).to_equal(true)
expect(boundary.should_offload).to_equal(false)
expect(winner.should_offload).to_equal(true)
```

</details>

#### fails closed without timing parity and device proof

- fails closed without timing parity and device proof
   - Expected: unavailable.available is false
   - Expected: unavailable.reason equals `timing-unavailable`
   - Expected: undersampled.should_offload is false
   - Expected: undersampled.reason equals `timing-unavailable`
   - Expected: mismatch.should_offload is false
   - Expected: mismatch.reason equals `pixel-mismatch`
   - Expected: unproven.should_offload is false
   - Expected: unproven.reason equals `device-proof-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed without timing parity and device proof")
val unavailable = web_gpu_paint_timing_evidence("cuda", 0, 0, 0, 0, 0, false, false, false)
val undersampled = web_gpu_paint_timing_evidence("cuda", 80, 100, 40, 60, 1, true, true, true)
val mismatch = web_gpu_paint_timing_evidence("cuda", 80, 100, 40, 60, 3, false, true, true)
val unproven = web_gpu_paint_timing_evidence("cuda", 80, 100, 40, 60, 3, true, true, false)
expect(unavailable.available).to_equal(false)
expect(unavailable.reason).to_equal("timing-unavailable")
expect(undersampled.should_offload).to_equal(false)
expect(undersampled.reason).to_equal("timing-unavailable")
expect(mismatch.should_offload).to_equal(false)
expect(mismatch.reason).to_equal("pixel-mismatch")
expect(unproven.should_offload).to_equal(false)
expect(unproven.reason).to_equal("device-proof-unavailable")
```

</details>

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3acd22a6f47e4d9823a157d92e1f081a352c263c1b89b10bf5e2f7443664fdb5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3acd22a6f47e4d9823a157d92e1f081a352c263c1b89b10bf5e2f7443664fdb5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3acd22a6f47e4d9823a157d92e1f081a352c263c1b89b10bf5e2f7443664fdb5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_gpu_paint_economics_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_gpu_paint_economics_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_gpu_paint_economics_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_gpu_paint_economics_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_gpu_paint_economics_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_gpu_paint_economics_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps cpu backends out of the gpu paint candidate set' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_gpu_paint_economics_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'offloads solid fills when transfer cost beats upload-bound presentation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_gpu_paint_economics_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'offloads when skipped CPU paint beats command overhead overall' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
