# GPU Dynamic Backend and Full Offload Feature Expert

## Selected contract

The selected provider architecture is Option A and the selected performance
policy is Tier 3. Final requirements are
`doc/02_requirements/feature/gpu_dynamic_backend_full_offload.md` and
`doc/02_requirements/nfr/gpu_dynamic_backend_full_offload.md`.

Providers export only `simple_gpu_provider_query_v1` and return the frozen
`SimpleGpuProviderAbiV1` table from
`src/runtime/simple_gpu_provider_abi_v1.h`. Do not restore per-symbol metadata
admission. Compatibility `rt_cuda_*`, `rt_vulkan_*`, and Metal byte adapters
resolve stable table slots from the admitted local handle.

## Invariants

- Query, callbacks, and shutdown execute outside the registry lock.
- Every callback owns a generation lease; unload rejects active calls/sessions.
- Device claims require completion, positive identities, device readback, exact
  checksum parity, zero mismatches, and no CPU fallback.
- Tier 3 promotes only below 50 us cached IR-to-submit p95 and at least 1.50x
  CPU throughput (or at most 0.67x CPU latency), with queue saturation and soak.
- Simple2D/Web/GUI/WM share Draw IR and Engine2D. Web/DB use coarse ProcessingIR;
  networking and durability remain CPU-owned.

## Canonical checks

```sh
sh scripts/check/check-gpu-provider-dynload-registry.shs --intensive
sh scripts/check/check-metal-provider-dynload-registry.shs --intensive
sh scripts/check/check-processing-ir-offload-fill-u32-break-even.shs RECEIPT
```

Provider-fixture PASS is not physical device evidence. The 2026-08-26 CUDA
RTX A6000 profile passed exact readback but remained CPU-selected. Native Metal,
production GUI/Web/WM, genuine DB kernels, and Stage4 SSpec/docgen remain open.

