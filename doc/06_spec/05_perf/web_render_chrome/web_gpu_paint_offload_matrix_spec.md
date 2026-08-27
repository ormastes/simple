# Web Gpu Paint Offload Matrix Specification

> Tests covering Simple Web GPU paint offload matrix.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Gpu Paint Offload Matrix Specification

## Scenarios

### Simple Web GPU paint offload matrix

#### backend combinations

<details>
<summary>Advanced: only treats GPU backends as paint offload candidates</summary>

#### only treats GPU backends as paint offload candidates _(slow)_

- only treats GPU backends as paint offload candidates
   - Expected: web_gpu_paint_backend_verdict("software") equals `cpu-backend-not-gpu-offload`
   - Expected: web_gpu_paint_backend_verdict("cpu") equals `cpu-backend-not-gpu-offload`
   - Expected: web_gpu_paint_backend_verdict("cpu_simd") equals `cpu-backend-not-gpu-offload`
   - Expected: web_gpu_paint_backend_verdict("cuda") equals `gpu-paint-candidate`
   - Expected: web_gpu_paint_backend_verdict("vulkan") equals `gpu-paint-candidate`
   - Expected: web_gpu_paint_backend_verdict("metal") equals `gpu-paint-candidate`
   - Expected: web_gpu_paint_backend_verdict("unknown") equals `unknown-backend-not-gpu-offload`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("only treats GPU backends as paint offload candidates")
expect(web_gpu_paint_backend_verdict("software")).to_equal("cpu-backend-not-gpu-offload")
expect(web_gpu_paint_backend_verdict("cpu")).to_equal("cpu-backend-not-gpu-offload")
expect(web_gpu_paint_backend_verdict("cpu_simd")).to_equal("cpu-backend-not-gpu-offload")
expect(web_gpu_paint_backend_verdict("cuda")).to_equal("gpu-paint-candidate")
expect(web_gpu_paint_backend_verdict("vulkan")).to_equal("gpu-paint-candidate")
expect(web_gpu_paint_backend_verdict("metal")).to_equal("gpu-paint-candidate")
expect(web_gpu_paint_backend_verdict("unknown")).to_equal("unknown-backend-not-gpu-offload")
```

</details>


</details>

<details>
<summary>Advanced: routes only estimated winning frames into the GPU paint candidate path</summary>

#### routes only estimated winning frames into the GPU paint candidate path _(slow)_

- routes only estimated winning frames into the GPU paint candidate path


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("routes only estimated winning frames into the GPU paint candidate path")
expect(simple_web_layout_render_html_should_gpu_paint(solid_full_frame_html(), 64, 64, "cuda", true)).to_be(true)
expect(simple_web_layout_render_html_should_gpu_paint(solid_full_frame_html(), 64, 64, "vulkan", true)).to_be(true)
expect(simple_web_layout_render_html_should_gpu_paint(solid_full_frame_html(), 64, 64, "metal", true)).to_be(true)
expect(simple_web_layout_render_html_should_gpu_paint(many_tiny_solid_html(), 16, 16, "vulkan", true)).to_be(false)
expect(simple_web_layout_render_html_should_gpu_paint(solid_full_frame_html(), 64, 64, "cpu_simd", true)).to_be(false)
expect(simple_web_layout_render_html_should_gpu_paint(solid_full_frame_html(), 64, 64, "vulkan", false)).to_be(false)
```

</details>


</details>

<details>
<summary>Advanced: reports why each backend and flag combination does or does not offload</summary>

#### reports why each backend and flag combination does or does not offload _(slow)_

- reports why each backend and flag combination does or does not offload
   - Expected: simple_web_layout_render_html_gpu_paint_route_verdict(solid_full_frame_html(), 64, 64, "cuda", true) equals `gpu-paint:gpu-paint-transfer-win:cpu-paint-offloaded:estimated-gpu-faster`
   - Expected: simple_web_layout_render_html_gpu_paint_route_verdict(solid_full_frame_html(), 64, 64, "vulkan", true) equals `gpu-paint:gpu-paint-transfer-win:cpu-paint-offloaded:estimated-gpu-faster`
   - Expected: simple_web_layout_render_html_gpu_paint_route_verdict(solid_full_frame_html(), 64, 64, "metal", true) equals `gpu-paint:gpu-paint-transfer-win:cpu-paint-offloaded:estimated-gpu-faster`
   - Expected: simple_web_layout_render_html_gpu_paint_route_verdict(many_tiny_solid_html(), 16, 16, "cuda", true) equals `cpu-mirror:communication-overhead:cpu-paint-offloaded:estimated-gpu-slower-ov... (full value in folded executable source)`
   - Expected: simple_web_layout_render_html_gpu_paint_route_verdict(many_tiny_solid_html(), 16, 16, "vulkan", true) equals `cpu-mirror:communication-overhead:cpu-paint-offloaded:estimated-gpu-slower-ov... (full value in folded executable source)`
   - Expected: simple_web_layout_render_html_gpu_paint_route_verdict(many_tiny_solid_html(), 16, 16, "metal", true) equals `cpu-mirror:communication-overhead:cpu-paint-offloaded:estimated-gpu-slower-ov... (full value in folded executable source)`
   - Expected: simple_web_layout_render_html_gpu_paint_route_verdict(solid_full_frame_html(), 64, 64, "cpu_simd", true) equals `cpu-backend-not-gpu-offload`
   - Expected: simple_web_layout_render_html_gpu_paint_route_verdict(solid_full_frame_html(), 64, 64, "unknown", true) equals `unknown-backend-not-gpu-offload`
   - Expected: simple_web_layout_render_html_gpu_paint_route_verdict(solid_full_frame_html(), 64, 64, "vulkan", false) equals `gpu-paint-disabled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("reports why each backend and flag combination does or does not offload")
expect(simple_web_layout_render_html_gpu_paint_route_verdict(solid_full_frame_html(), 64, 64, "cuda", true)).to_equal("gpu-paint:gpu-paint-transfer-win:cpu-paint-offloaded:estimated-gpu-faster")
expect(simple_web_layout_render_html_gpu_paint_route_verdict(solid_full_frame_html(), 64, 64, "vulkan", true)).to_equal("gpu-paint:gpu-paint-transfer-win:cpu-paint-offloaded:estimated-gpu-faster")
expect(simple_web_layout_render_html_gpu_paint_route_verdict(solid_full_frame_html(), 64, 64, "metal", true)).to_equal("gpu-paint:gpu-paint-transfer-win:cpu-paint-offloaded:estimated-gpu-faster")
expect(simple_web_layout_render_html_gpu_paint_route_verdict(many_tiny_solid_html(), 16, 16, "cuda", true)).to_equal("cpu-mirror:communication-overhead:cpu-paint-offloaded:estimated-gpu-slower-overhead")
expect(simple_web_layout_render_html_gpu_paint_route_verdict(many_tiny_solid_html(), 16, 16, "vulkan", true)).to_equal("cpu-mirror:communication-overhead:cpu-paint-offloaded:estimated-gpu-slower-overhead")
expect(simple_web_layout_render_html_gpu_paint_route_verdict(many_tiny_solid_html(), 16, 16, "metal", true)).to_equal("cpu-mirror:communication-overhead:cpu-paint-offloaded:estimated-gpu-slower-overhead")
expect(simple_web_layout_render_html_gpu_paint_route_verdict(solid_full_frame_html(), 64, 64, "cpu_simd", true)).to_equal("cpu-backend-not-gpu-offload")
expect(simple_web_layout_render_html_gpu_paint_route_verdict(solid_full_frame_html(), 64, 64, "unknown", true)).to_equal("unknown-backend-not-gpu-offload")
expect(simple_web_layout_render_html_gpu_paint_route_verdict(solid_full_frame_html(), 64, 64, "vulkan", false)).to_equal("gpu-paint-disabled")
```

</details>


</details>

<details>
<summary>Advanced: keeps exact output regardless of the measured route</summary>

#### keeps exact output regardless of the measured route _(slow)_

- keeps exact output regardless of the measured route
   - Expected: readback.pixels.len() equals `16 * 16`
   - Expected: readback.pixels equals `oracle.pixels`
   - Expected: readback.pixels[readback.pixels.len() - 1] equals `0xFF0F172Au32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("keeps exact output regardless of the measured route")
val html = many_tiny_solid_html_with_canvas()
val readback = simple_web_layout_render_html_readback_paint(html, 16, 16, "vulkan", true)
val oracle = simple_web_layout_render_html_readback_paint(html, 16, 16, "cpu", false)
expect(readback.pixels.len()).to_equal(16 * 16)
expect(readback.pixels).to_equal(oracle.pixels)
expect(readback.pixels[readback.pixels.len() - 1]).to_equal(0xFF0F172Au32)
```

</details>


</details>

#### CPU paint and communication economics

<details>
<summary>Advanced: offloads when solid fill paint avoids CPU paint and transfer wins</summary>

#### offloads when solid fill paint avoids CPU paint and transfer wins _(slow)_

- offloads when solid fill paint avoids CPU paint and transfer wins
   - Expected: economics.cpu_paint_pixels equals `0`
   - Expected: frame.fb.len() equals `0`
   - Expected: economics.should_offload is true
   - Expected: economics.cpu_job_verdict equals `cpu-paint-offloaded`
   - Expected: economics.speed_verdict equals `estimated-gpu-faster`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("offloads when solid fill paint avoids CPU paint and transfer wins")
val frame = simple_web_layout_render_html_gpu_frame(solid_full_frame_html(), 64, 64)
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.cpu_paint_pixels).to_equal(0)
expect(frame.fb.len()).to_equal(0)
expect(economics.fill_pixels).to_be_greater_than(0)
expect(economics.gpu_paint_transfer_pixels).to_be_less_than(economics.upload_bound_transfer_pixels)
expect(economics.gpu_paint_total_pixels).to_be_less_than(economics.upload_bound_total_pixels)
expect(economics.should_offload).to_equal(true)
expect(economics.cpu_job_verdict).to_equal("cpu-paint-offloaded")
expect(economics.speed_verdict).to_equal("estimated-gpu-faster")
```

</details>


</details>

<details>
<summary>Advanced: offloads when transfer loses but saved CPU paint makes total work win</summary>

#### offloads when transfer loses but saved CPU paint makes total work win _(slow)_

- offloads when transfer loses but saved CPU paint makes total work win
   - Expected: economics.cpu_paint_pixels equals `0`
   - Expected: economics.should_offload is true
   - Expected: economics.reason equals `gpu-paint-total-win`
   - Expected: economics.cpu_job_verdict equals `cpu-paint-offloaded`
   - Expected: economics.speed_verdict equals `estimated-gpu-faster`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("offloads when transfer loses but saved CPU paint makes total work win")
val frame = direct_frame(16, 16, 0, 0, 0, 16, 16)
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.cpu_paint_pixels).to_equal(0)
expect(economics.gpu_paint_transfer_pixels).to_be_greater_than(economics.upload_bound_transfer_pixels)
expect(economics.gpu_paint_total_pixels).to_be_less_than(economics.upload_bound_total_pixels)
expect(economics.should_offload).to_equal(true)
expect(economics.reason).to_equal("gpu-paint-total-win")
expect(economics.cpu_job_verdict).to_equal("cpu-paint-offloaded")
expect(economics.speed_verdict).to_equal("estimated-gpu-faster")
```

</details>


</details>

<details>
<summary>Advanced: does not claim offload when CPU ground truth is still required</summary>

#### does not claim offload when CPU ground truth is still required _(slow)_

- does not claim offload when CPU ground truth is still required
   - Expected: economics.cpu_paint_pixels equals `64 * 64`
   - Expected: economics.should_offload is false
   - Expected: economics.reason equals `cpu-ground-truth-required`
   - Expected: economics.cpu_job_verdict equals `cpu-paint-required`
   - Expected: economics.speed_verdict equals `not-offloaded`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("does not claim offload when CPU ground truth is still required")
val frame = simple_web_layout_render_html_gpu_frame(text_and_solid_html(), 64, 64)
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.cpu_paint_pixels).to_equal(64 * 64)
expect(economics.should_offload).to_equal(false)
expect(economics.reason).to_equal("cpu-ground-truth-required")
expect(economics.cpu_job_verdict).to_equal("cpu-paint-required")
expect(economics.speed_verdict).to_equal("not-offloaded")
```

</details>


</details>

<details>
<summary>Advanced: rejects command-heavy tiny fills when communication overhead loses</summary>

#### rejects command-heavy tiny fills when communication overhead loses _(slow)_

- rejects command-heavy tiny fills when communication overhead loses
   - Expected: economics.cpu_paint_pixels equals `0`
   - Expected: economics.gpu_paint_total_pixels equals `economics.upload_bound_total_pixels`
   - Expected: economics.should_offload is false
   - Expected: economics.reason equals `communication-overhead`
   - Expected: economics.cpu_job_verdict equals `cpu-paint-offloaded`
   - Expected: economics.speed_verdict equals `estimated-gpu-slower-overhead`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("rejects command-heavy tiny fills when communication overhead loses")
val frame = simple_web_layout_render_html_gpu_frame(many_tiny_solid_html(), 16, 16)
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.cpu_paint_pixels).to_equal(0)
expect(economics.fill_op_count).to_be_greater_than(7)
expect(economics.gpu_paint_transfer_pixels).to_be_greater_than(economics.upload_bound_transfer_pixels)
expect(economics.gpu_paint_total_pixels).to_equal(economics.upload_bound_total_pixels)
expect(economics.should_offload).to_equal(false)
expect(economics.reason).to_equal("communication-overhead")
expect(economics.cpu_job_verdict).to_equal("cpu-paint-offloaded")
expect(economics.speed_verdict).to_equal("estimated-gpu-slower-overhead")
```

</details>


</details>

<details>
<summary>Advanced: keeps exact break-even work on CPU instead of claiming offload</summary>

#### keeps exact break-even work on CPU instead of claiming offload _(slow)_

- keeps exact break-even work on CPU instead of claiming offload
   - Expected: economics.cpu_paint_pixels equals `192`
   - Expected: economics.gpu_paint_total_pixels equals `economics.upload_bound_total_pixels`
   - Expected: economics.should_offload is false
   - Expected: economics.reason equals `communication-overhead`
   - Expected: economics.speed_verdict equals `estimated-gpu-slower-overhead`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("keeps exact break-even work on CPU instead of claiming offload")
val frame = direct_frame(16, 16, 192, 0, 0, 16, 16)
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.cpu_paint_pixels).to_equal(192)
expect(economics.gpu_paint_total_pixels).to_equal(economics.upload_bound_total_pixels)
expect(economics.should_offload).to_equal(false)
expect(economics.reason).to_equal("communication-overhead")
expect(economics.speed_verdict).to_equal("estimated-gpu-slower-overhead")
```

</details>


</details>

<details>
<summary>Advanced: rejects offload when saved CPU paint is not enough to beat total work</summary>

#### rejects offload when saved CPU paint is not enough to beat total work _(slow)_

- rejects offload when saved CPU paint is not enough to beat total work
   - Expected: economics.cpu_paint_pixels equals `193`
   - Expected: economics.should_offload is false
   - Expected: economics.reason equals `communication-overhead`
   - Expected: economics.cpu_job_verdict equals `cpu-paint-offloaded`
   - Expected: economics.speed_verdict equals `estimated-gpu-slower-overhead`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("rejects offload when saved CPU paint is not enough to beat total work")
val frame = direct_frame(16, 16, 193, 0, 0, 16, 16)
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.cpu_paint_pixels).to_equal(193)
expect(economics.gpu_paint_total_pixels).to_be_greater_than(economics.upload_bound_total_pixels)
expect(economics.should_offload).to_equal(false)
expect(economics.reason).to_equal("communication-overhead")
expect(economics.cpu_job_verdict).to_equal("cpu-paint-offloaded")
expect(economics.speed_verdict).to_equal("estimated-gpu-slower-overhead")
```

</details>


</details>

<details>
<summary>Advanced: does not treat skipped CPU work as offload when there are no fill commands</summary>

#### does not treat skipped CPU work as offload when there are no fill commands _(slow)_

- does not treat skipped CPU work as offload when there are no fill commands
   - Expected: economics.cpu_paint_pixels equals `0`
   - Expected: economics.fill_op_count equals `0`
   - Expected: economics.should_offload is false
   - Expected: economics.reason equals `no-gpu-fill-ops`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("does not treat skipped CPU work as offload when there are no fill commands")
val frame = WebGpuPaintFrame(fb: [0xFFFFFFFFu32; 16 * 16], fill_ops: [], width: 16, height: 16, base: 0xFFFFFFFFu32, cpu_paint_pixels: 0)
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.cpu_paint_pixels).to_equal(0)
expect(economics.fill_op_count).to_equal(0)
expect(economics.should_offload).to_equal(false)
expect(economics.reason).to_equal("no-gpu-fill-ops")
```

</details>


</details>

<details>
<summary>Advanced: rejects offscreen fill commands that do no clipped GPU work</summary>

#### rejects offscreen fill commands that do no clipped GPU work _(slow)_

- rejects offscreen fill commands that do no clipped GPU work
   - Expected: economics.cpu_paint_pixels equals `0`
   - Expected: economics.fill_op_count equals `1`
   - Expected: economics.fill_pixels equals `0`
   - Expected: economics.should_offload is false
   - Expected: economics.reason equals `no-clipped-fill-pixels`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("rejects offscreen fill commands that do no clipped GPU work")
val frame = direct_frame(16, 16, 0, 32, 32, 8, 8)
val economics = web_gpu_paint_economics(frame, 0xFFFFFFFFu32)
expect(economics.cpu_paint_pixels).to_equal(0)
expect(economics.fill_op_count).to_equal(1)
expect(economics.fill_pixels).to_equal(0)
expect(economics.should_offload).to_equal(false)
expect(economics.reason).to_equal("no-clipped-fill-pixels")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/web_render_chrome/web_gpu_paint_offload_matrix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Simple Web GPU paint offload matrix.
- Simple Web GPU paint offload matrix

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 12 |
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

- Canonical SPipe generation for source `e512db9e4b401008a639bff2736087d43d6f52a4768f2fda118b4ea6b22a1806`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e512db9e4b401008a639bff2736087d43d6f52a4768f2fda118b4ea6b22a1806`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e512db9e4b401008a639bff2736087d43d6f52a4768f2fda118b4ea6b22a1806`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/05_perf/web_render_chrome/web_gpu_paint_offload_matrix_spec.spl
mirror: doc/06_spec/05_perf/web_render_chrome/web_gpu_paint_offload_matrix_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/web_render_chrome/web_gpu_paint_offload_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/web_render_chrome/web_gpu_paint_offload_matrix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/web_render_chrome/web_gpu_paint_offload_matrix_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/05_perf/web_render_chrome/web_gpu_paint_offload_matrix_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'only treats GPU backends as paint offload candidates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/web_render_chrome/web_gpu_paint_offload_matrix_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes only estimated winning frames into the GPU paint candidate path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/web_render_chrome/web_gpu_paint_offload_matrix_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports why each backend and flag combination does or does not offload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
