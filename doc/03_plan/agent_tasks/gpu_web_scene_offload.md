# GPU Web Scene Offload Agent Tasks

| Lane | Owner | Output | Status |
|---|---|---|---|
| Local event-path audit | Hume | ownership and reusable seams | complete |
| GPU synchronization research | Rawls | Vulkan/WebGPU/Metal constraints | complete |
| Documentation contradiction audit | Faraday | canonical slug and superseded claims | complete |
| Boundary contract and integration | `/root` | v2 request/receipt/executor API, then HostCompositor adapter | host adapter pending |
| Vulkan/WebGPU device kernel | N/A | real backend receipt writer | future lane |

Merge owner and final reviewer: `/root`. Sidecar findings are accepted only
after source-level review. Shared interface:
`Simple2dGpuEventBoundaryManager`; frozen visible steps: “forward ordered
input”, “execute GPU event epoch”, “fall back with reason”, and “project state
through Web → GUI → WM”.
