# TL;DR — std.compute & ExecTarget

Config-selectable CPU/GPU compute stdlib. Tag the **device class**; runtime resolves the
**backend** (SYCL `device_type` model).

- **L1 class:** `default cpu simd_cpu gpu fpga simd` → **L2 backend (auto):**
  `cuda hip opencl vulkan metal webgpu vhdl neon scalar`.
- **Config:** `SIMPLE_COMPUTE_TARGET/BACKEND/ENFORCE`; `suggest`=soft fallback,
  `require`=hard fail-closed (rt_exit 70).
- **Algorithms** (generic `T`, take `ExecTarget`): reduce, transform, scan, sort, count,
  filter, find, min/max_element, transform_reduce, unique, lower_bound, binary_search.
  CPU path = differential oracle. Use `less` comparators; avoid generic `!=` (interp bug).
- **Containers:** `Span<T>`, `FixedArray<T>`, `InplaceVector<T>`.
- **Backed kernels:** real CUDA/HIP/OpenCL/Metal/WebGPU source (transform-scale, saxpy),
  emission-verified. GPU hardware execution = open.
- 60 specs green. Full guide: `exec_target_compute_stdlib.md`.

<!-- sdn-diagram:id=std_compute.tldr -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=std_compute.tldr hash=sha256:auto render=ascii
@layout dag
@direction LR

Config -> ExecTarget
ExecTarget -> Backend
Backend -> AlgorithmSurface
AlgorithmSurface -> CPU_oracle
AlgorithmSurface -> GPU_kernels
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=std_compute.tldr hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->
