# Compute Dispatch Specification

> <details>

<!-- sdn-diagram:id=compute_dispatch_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=compute_dispatch_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

compute_dispatch_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=compute_dispatch_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compute Dispatch Specification

## Scenarios

### ComputeDispatch

#### selects the best available compute backend in policy order

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = ComputeDispatch.auto()

expect(_valid_dispatch_name(result.selected_name)).to_equal(true)
expect(result.probe.has_compute).to_equal(true)
expect(result.probe.status == BackendStatus.Initialized).to_equal(true)
```

</details>

#### module helper returns the same available dispatch shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = compute_dispatch_auto()

expect(_valid_dispatch_name(result.selected_name)).to_equal(true)
expect(result.is_available()).to_equal(true)
```

</details>

#### records launch and frame synchronization counters

1. var result = ComputeDispatch auto
2. result record launch
   - Expected: result.synchronize_frame() is true
   - Expected: result.hits.kernel_launches equals `1`
   - Expected: result.hits.synchronize_calls equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = ComputeDispatch.auto()

result.record_launch()
expect(result.synchronize_frame()).to_equal(true)
expect(result.hits.kernel_launches).to_equal(1)
expect(result.hits.synchronize_calls).to_equal(1)
expect(result.summary()).to_contain("dispatch selected=")
```

</details>

#### routes explicit backend requests through strict factory probe results

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cpu = compute_dispatch_for_backend("cpu")
val unknown = compute_dispatch_for_backend("definitely_missing_backend")

expect(cpu.selected_name).to_equal("cpu")
expect(cpu.is_available()).to_equal(true)
expect(unknown.is_available()).to_equal(false)
expect(unknown.probe.status == BackendStatus.Failed).to_equal(true)
```

</details>

#### synchronizes and submits a BackendFrame through the dispatch result

1. var result = ComputeDispatch auto
2. var frame = BackendFrame create
   - Expected: result.synchronize_backend_frame(frame) equals `ok`
   - Expected: frame.submitted is true
   - Expected: result.hits.synchronize_calls equals `1`
   - Expected: result.synchronize_backend_frame(frame) equals `already_submitted`
   - Expected: result.hits.synchronize_calls equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = ComputeDispatch.auto()
var frame = BackendFrame.create(42, 7, 64, 32)

expect(result.synchronize_backend_frame(frame)).to_equal("ok")
expect(frame.submitted).to_equal(true)
expect(result.hits.synchronize_calls).to_equal(1)
expect(result.synchronize_backend_frame(frame)).to_equal("already_submitted")
expect(result.hits.synchronize_calls).to_equal(2)
```

</details>

#### exports CPU SIMD hit counters through dispatch results

1. var result = compute dispatch for backend
2. reset simd hits
3. fill span
4. copy span
5. alpha blend span
6. simd blit rect
7. simd scroll region
8. result refresh hit counts
   - Expected: result.hits.simd_fill_hits equals `1`
   - Expected: result.hits.simd_copy_hits equals `1`
   - Expected: result.hits.simd_alpha_hits equals `1`
   - Expected: result.hits.simd_blit_hits equals `1`
   - Expected: result.hits.simd_scroll_hits equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var result = compute_dispatch_for_backend("cpu_simd_x86")
reset_simd_hits()
var pixels: [u32] = [0u32; 16]
var src: [u32] = [0xFF112233; 16]
var alpha_src: [u32] = [0x80FF0000; 16]

fill_span(pixels, 0, 4, 0xFF010203)
copy_span(pixels, 4, src, 0, 4)
alpha_blend_span(pixels, alpha_src, 8, 4)
simd_blit_rect(pixels, 4, 0, 3, src, 4, 0, 0, 4, 1)
simd_scroll_region(pixels, 4, 0, 0, 4, 4, 1)
result.refresh_hit_counts()

expect(result.hits.simd_fill_hits).to_equal(1)
expect(result.hits.simd_copy_hits).to_equal(1)
expect(result.hits.simd_alpha_hits).to_equal(1)
expect(result.hits.simd_blit_hits).to_equal(1)
expect(result.hits.simd_scroll_hits).to_equal(1)
expect(result.summary()).to_contain("simd_fill=1")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/compute_dispatch_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ComputeDispatch

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
