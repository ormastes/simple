# TL;DR — Unified CPU/GPU Compute Stdlib Rollout

One generic, config-switchable compute surface in `nogc_async_mut`: libcu++-parity types +
Thrust-parity algorithms, compiled through existing `gpu_portable_compute`/`@gpu_kernel`
(no fork). Dispatch by one `ExecTarget` resolver. CUDA built first = backend + oracle;
delivery CUDA → pure-Simple → Vulkan → Metal. Co-goal: fix the Simple bugs it depends on.

- **Pre-work (P1–P5):** one resolver, `ExecTarget` policy, iterator bug, f64 triage,
  de-masquerade `gpu_*`.
- **Cell grid:** `{algorithm} × {backend}`, each = disjoint file scope (parallel unit).
- **Waves:** W1 CUDA oracle → W2 pure-Simple (the no-GPU win) → W3 Vulkan → W4 Metal.
- **Verify gate (Opus):** differential vs CUDA oracle (bit-exact int/sort, tolerance for
  float), perf-vs-CPU, fail-closed `rt_exit 70`. One commit per cell.
- **Milestones:** M0 switch proven · M1 oracle · M2 pure-Simple · M3 Vk+Metal · M4 type parity.

SPipe: `.spipe/gpu_containers_unified/state.md` (AC-1…AC-7). Full plan:
`unified_compute_stdlib_rollout_2026-06-16.md`. Next: `/arch` (resolve Q1/Q3/Q4).

<!-- sdn-diagram:id=gpu_containers_unified.plan_tldr -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gpu_containers_unified.plan_tldr hash=sha256:auto render=ascii
@layout dag
@direction LR

PreWork -> CUDA_oracle
CUDA_oracle -> pure_Simple
CUDA_oracle -> Vulkan
CUDA_oracle -> Metal
pure_Simple -> Verify_gate
Vulkan -> Verify_gate
Metal -> Verify_gate
Verify_gate -> Merge
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gpu_containers_unified.plan_tldr hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->
