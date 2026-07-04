<!-- codex-research -->
# Simple 3D Graph IR Requirements

## Scope

Add a backend-neutral Graph IR for the existing Simple 3D render library.

## Requirements

| Requirement | Statement |
|-------------|-----------|
| REQ-3D-GRAPH-001 | The library records 3D render passes, resources, and indexed mesh draws without depending on a specific GPU backend. |
| REQ-3D-GRAPH-002 | The library provides a deterministic optimization pass that dedupes resource references and batches draw order inside each pass by backend-relevant state. |
| REQ-3D-GRAPH-003 | The optimized graph can be replayed through the existing `RenderBackend3D` trait. |

## Out of Scope

- New CUDA kernel graph execution.
- Rewriting Vulkan/WebGPU command recorders.
- Solving the existing raw float/index byte serialization limitation in mesh
  upload.
