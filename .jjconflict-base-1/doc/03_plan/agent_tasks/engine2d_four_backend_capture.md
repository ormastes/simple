# Engine2D Four-Backend Capture Agent Tasks

Base revision: `576be2a487`.

| Lane | Owned range | Deliverable |
|---|---|---|
| Metal | Metal backend/session, Metal wrappers/specs/evidence | Live Metal capture + events |
| Vulkan | Vulkan backend/session/font, Vulkan wrappers/specs/evidence | Live Vulkan capture + events |
| QEMU | SimpleOS compositor, x86/ARM runtime target, QEMU wrappers/specs | x86_64 + ARM64 SIMD captures/events |
| Merge owner | shared Engine2D, host SIMD, `wm_compare`, docs | integrated comparison and push |

Shared files (`engine.spl`, `backend.spl`, Draw IR schema, and `wm_compare`) are
owned only by the merge lane. Backend agents report required common changes.

Lower-model sidecars: `N/A`; the available agents are normal-capability agents
with narrow platform ownership. Merge owner and final highest-capability
reviewer: `/root`.

Frozen types, helpers, and manual steps are defined in the detail design.
Unsupported live behavior must use an explicit failing assertion or rejection
status until implemented.
