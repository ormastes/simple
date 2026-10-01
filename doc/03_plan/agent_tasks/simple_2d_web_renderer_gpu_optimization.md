# Agent tasks — Simple 2D/web GPU optimization

Merge owner and final highest-capability reviewer: `/root`.

| Lane | Ownership | Stop condition |
|---|---|---|
| Chrome ABI | `tools/chromium-primitive-oracle/**`, loader/spec | Real dylib and semantic broker receipt; GPU remains fail-closed. |
| Surface contracts | new Engine2D session types/specs | Frozen state/token/receipt names and transition coverage. |
| Vulkan async | Vulkan adapter/backend focused files | Real fence token, ring, nonblocking poll, present/capture split. |
| Web integration | browser presenter/fast route focused files | Surface lifecycle, zero steady readback, event damage deltas. |
| Benchmarks | C/Simple and Chrome/Simple collectors | Same workload/interval metadata and admitted p50/p95/RSS rows. |
| SPipe/manual | system/perf specs and mirrored docs | Every requirement traced; no placeholder pass or raw-mechanics manual. |

Sidecars: N/A until shared names `GpuRenderSurfaceId`, `GpuFrameSlot`,
`GpuSubmissionToken`, `GpuPresentReceipt`, `GpuCaptureReceipt`, and
`GpuSurfaceMemoryReceipt` plus scenario step names above are accepted. Each lane
must preserve unrelated dirty files and report its exact path set.
