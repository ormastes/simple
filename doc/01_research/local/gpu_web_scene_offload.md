# GPU Web Scene Offload — Local Research

Updated 2026-08-02 after parallel source and documentation audits.

The repository already has a deterministic CPU oracle in
`common.ui.gpu_event_core` and `gpu_web_event_model`: normalization,
coalescing, hit routes, capture/target/bubble order, mutation journals, epoch
hashing, apply, and rollback. `gpu_web_ports` supplies the v1 fixed-width event
ABI. Engine2D's `host_gpu_event_queue` supplies queue and hit-query transport,
but its completion is host telemetry and is not proof that a device executed an
event kernel.

Current production dispatch remains fragmented and CPU-owned in the OS
compositor, hosted WM, bare-metal WM, hosted browser, and Web DOM backend. The
canonical target plan is
`doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md`; older documents that
freeze semantic events permanently on CPU are superseded for GPU-eligible
bounded events, while remaining correct for fallback and privileged effects.

The missing seam is a Simple2D boundary manager that distinguishes submission
from device completion, validates sequence/scene/boundary/hash/commit identity,
and assigns exactly one commit owner. `simple2d_gpu_event_boundary.spl` adds
that v2 contract. A backend kernel and production compositor integration remain
required before claiming device event execution.

