# Agent Tasks — Web Renderer Vulkan 4K Showcase Hardening

| Lane | Owner | Deliverable |
|---|---|---|
| Inventory audit | sidecar (complete) | Production traceability gaps and false rows. |
| Showcase/tab audit | sidecar (complete) | Canonical entrypoint, accessibility, installed-launch gaps. |
| Vulkan/Chrome perf audit | sidecar (complete) | Real vs synthetic evidence and receipt gaps. |
| Architecture/API/spec merge | root Codex | Shared interfaces, docs, executable scenarios. |
| Implementation/refactor | root Codex | Inventory, tab model, runner restoration, evidence contracts. |
| Final review | highest-capability root Codex | Requirement-by-requirement verify verdict. |

Shared interfaces and manual/helper names are fixed in `.spipe/web_renderer_vulkan_4k_showcase_hardening/state.md`. Any unresolved scaffold must fail with `assert(false)` or `fail(...)`; no sidecar may claim broad completion from lexical/source-only evidence. Merge owner and generated-manual review owner: root Codex.

2026-09-05 Astra design review: architecture/detail design, GUI contract, test plan and authored manual now distinguish required behavior from implemented scaffolding. The review identifies native tab dispatch, actual per-row demonstrations, source-bound launch-to-present receipts and complete visual comparison as outstanding integrations. Astra review approves retaining the existing renderer ownership boundaries; it does not certify implementation, runtime performance or final verification PASS. Root coordinates the independently owned implementation lanes and remains responsible for final integration review.
