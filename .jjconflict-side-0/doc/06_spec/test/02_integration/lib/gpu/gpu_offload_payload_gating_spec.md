# GPU Offload Payload-Gating Discriminator

> A claim that work ran on the GPU must be *discriminated*, not merely observed.

<!-- sdn-diagram:id=gpu_offload_payload_gating_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_offload_payload_gating_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gpu_offload_payload_gating_spec -> std
gpu_offload_payload_gating_spec -> test
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_offload_payload_gating_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU Offload Payload-Gating Discriminator

A claim that work ran on the GPU must be *discriminated*, not merely observed.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Testing \| **Status:** In Progress |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md |
| Design | N/A |
| Research | N/A |
| Source | `test/02_integration/lib/gpu/gpu_offload_payload_gating_spec.spl` |
| Updated | 2026-07-15 |
| Generator | manually synchronized; `simple spipe-docgen` refresh pending |

A claim that work ran on the GPU must be *discriminated*, not merely observed.
One honest gate is proven here across backends:

1. **std.compute** is a payload-gated simulation: it always computes the CPU
   reference and only reports GPU provenance. With no payload the CPU ran; with
   a payload the provenance flips — the value must equal the CPU oracle in
   BOTH branches. ExecTarget enforcement is proven too: `suggest` falls back
   (resolved), `require` of an absent GPU fails closed (unresolved).
Every backend runs the SAME shared body, so backend coverage is data-driven.

## Scenarios

### compute-surface payload gating per backend

#### gates CUDA offload on the payload without changing the value

- Dispatch a reduce on a CUDA target with and without a payload
- assert payload gating


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch a reduce on a CUDA target with and without a payload")
assert_payload_gating(ComputeBackend.Cuda)
```

</details>

#### gates HIP offload on the payload without changing the value

- Dispatch a reduce on a HIP target with and without a payload
- assert payload gating


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch a reduce on a HIP target with and without a payload")
assert_payload_gating(ComputeBackend.Hip)
```

</details>

#### gates OpenCL offload on the payload without changing the value

- Dispatch a reduce on an OpenCL target with and without a payload
- assert payload gating


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch a reduce on an OpenCL target with and without a payload")
assert_payload_gating(ComputeBackend.OpenCl)
```

</details>

#### gates Vulkan offload on the payload without changing the value

- Dispatch a reduce on a Vulkan target with and without a payload
- assert payload gating


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch a reduce on a Vulkan target with and without a payload")
assert_payload_gating(ComputeBackend.Vulkan)
```

</details>

#### gates Metal offload on the payload without changing the value

- Dispatch a reduce on a Metal target with and without a payload
- assert payload gating


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch a reduce on a Metal target with and without a payload")
assert_payload_gating(ComputeBackend.Metal)
```

</details>

#### gates WebGPU offload on the payload without changing the value

- Dispatch a reduce on a WebGPU target with and without a payload
- assert payload gating


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Dispatch a reduce on a WebGPU target with and without a payload")
assert_payload_gating(ComputeBackend.WebGpu)
```

</details>

### ExecTarget enforcement

#### suggests a GPU class and falls back to CPU on a bare machine

- Resolve a GPU class in SUGGEST mode with no GPU caps
- assert suggest falls back


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve a GPU class in SUGGEST mode with no GPU caps")
assert_suggest_falls_back()
```

</details>

#### requires a GPU class and fails closed on a bare machine

- Resolve a GPU class in REQUIRE mode with no GPU caps
- assert require absent fails closed


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Resolve a GPU class in REQUIRE mode with no GPU caps")
assert_require_absent_fails_closed()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md](doc/03_plan/ui/testing/gpu_draw_event_intensive_tests.md)


</details>
