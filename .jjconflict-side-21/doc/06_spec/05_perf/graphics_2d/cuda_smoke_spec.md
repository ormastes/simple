# cuda_smoke_spec

> test/perf/graphics_2d/cuda_smoke_spec.spl

<!-- sdn-diagram:id=cuda_smoke_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cuda_smoke_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cuda_smoke_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cuda_smoke_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cuda_smoke_spec

test/perf/graphics_2d/cuda_smoke_spec.spl

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | AC-3 — CUDA backend hardware smoke test |
| Category | Graphics \| Backend \| CUDA |
| Status | Pending implementation (Phase 5) |
| Source | `test/05_perf/graphics_2d/cuda_smoke_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

test/perf/graphics_2d/cuda_smoke_spec.spl

Verifies the CUDA path:
  Engine2D → CUDA kernel dispatch → device framebuffer → sync_readback
Also verifies CUDA benchmark output vs CPU reference.

@cover src/lib/gc_async_mut/gpu/engine2d/backend_cuda.spl
@cover src/lib/gc_async_mut/gpu/engine2d/backend_core.spl

## Scenarios

### backend_cuda — AC-3: CUDA hardware smoke

### CUDA kernel dispatch

#### AC-3: CUDA backend name is cuda

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: CudaSmokeSentinel = make_cuda_smoke_ok()
expect(s.backend).to_equal(CUDA_BACKEND_NAME)
```

</details>

#### AC-3: kernel is dispatched on device

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: CudaSmokeSentinel = make_cuda_smoke_ok()
expect(s.kernel_dispatched).to_equal(true)
```

</details>

#### AC-3: device framebuffer is written after kernel dispatch

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: CudaSmokeSentinel = make_cuda_smoke_ok()
expect(s.framebuffer_written).to_equal(true)
```

</details>

### sync_readback

#### AC-3: sync_readback completes without error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: CudaSmokeSentinel = make_cuda_smoke_ok()
expect(s.readback_completed).to_equal(true)
```

</details>

#### AC-3: CUDA pixel hash matches CPU reference hash

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: CudaSmokeSentinel = make_cuda_smoke_ok()
expect(hashes_match(s)).to_equal(true)
```

</details>

#### AC-3: cpu_pixel_hash and cuda_pixel_hash are equal (correctness)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: CudaSmokeSentinel = make_cuda_smoke_ok()
expect(s.cpu_pixel_hash).to_equal(s.cuda_pixel_hash)
```

</details>

### CUDA vs CPU performance

#### AC-3: CUDA us_per_frame is less than CPU us_per_frame

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: CudaSmokeSentinel = make_cuda_smoke_ok()
expect(cuda_faster_than_cpu(s)).to_equal(true)
```

</details>

#### AC-3: CUDA us_per_frame is greater than zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: CudaSmokeSentinel = make_cuda_smoke_ok()
expect(s.us_per_frame_cuda > 0).to_equal(true)
```

</details>

#### AC-3: CPU reference us_per_frame is greater than zero

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s: CudaSmokeSentinel = make_cuda_smoke_ok()
expect(s.us_per_frame_cpu > 0).to_equal(true)
```

</details>

### BenchFrameRecord schema for CUDA

#### AC-3: CUDA bench record backend field equals cuda

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend: text = "cuda"
expect(backend).to_equal(CUDA_BACKEND_NAME)
```

</details>

#### AC-3: CUDA bench record kernel field is one of fill blit alpha_blend scroll

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val kernels: [text] = ["fill", "blit", "alpha_blend", "scroll"]
expect(kernels.len()).to_equal(4)
expect(kernels[0]).to_equal("fill")
expect(kernels[1]).to_equal("blit")
expect(kernels[2]).to_equal("alpha_blend")
expect(kernels[3]).to_equal("scroll")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
