<!-- codex-architecture -->
# Browser GPU surface owner — TLDR

Selected O1 + B/N2. `BrowserRenderer` is a pixel facade and BrowserSession
recreates it per render. Its global Engine2D caches cannot own display lifetime.

The real window owner already lives in `Engine2dCompositorBackend`, reached
from `host_compositor_core.spl`. Its Vulkan present receipts are real, but
compute submission waits synchronously. O1 adds the surface capsule there; B/N2
provides one runtime-owned tunable bounded session per device generation.

One device scheduler holds aggregate admission; each surface owns resources and
pending damage. Submission, compute completion and presenter release are distinct.
Only the latter acknowledges events and permits reused image storage. Three
slots need per-image revision history or proven GPU ordering for shared images.

Resize/close retire only the affected surface. Device loss revokes publication
immediately and retains unresolved work under device recovery. Global cache
drains and scalar model tokens cannot prove either operation.

Next: `browser_renderer_gpu_surface_owner.md`,
`../02_requirements/feature/browser_renderer_gpu_surface_owner.md`,
`../02_requirements/feature/vulkan_async_compute_submission_ring.md`,
`../03_plan/sys_test/browser_renderer_gpu_surface_owner.md`.

Current blocker: V2 candidate removed after two Sol cycles and Astra review;
no real provider/consumer existed, and its capability accepted local identity.
Repair the managed-buffer SFFI export gap, then the real existing-session and
presenter boundary. Exact handoff:
`../09_report/gpu_async_device_port_v2_astra_review_2026-09-09.md`.
