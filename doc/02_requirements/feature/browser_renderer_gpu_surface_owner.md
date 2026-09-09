<!-- codex-requirements -->
# Browser renderer GPU surface owner

**Status:** selected for implementation
**Selection:** O1 — compositor-owned surfaces + B/N2 — runtime-owned tunable bounded submission session
**Evidence date:** 2026-09-09
**Parent feature:** `simple_2d_web_renderer_gpu_optimization.md`

The production display host owns the GPU device scheduler and the bounded
child-surface table. Browser producers send immutable scene/resource snapshots
and generation-checked damage deltas to that owner. The Vulkan runtime owns the
device admission lease and the B/N2 submission session; Simple owns only copied
surface receipts and pending producer data. Browser code never receives raw
Vulkan handles or physical resource ownership.

## Functional requirements

- **REQ-SURFACE-001 — compositor ownership:** A hosted browser surface is
  opened, offered, polled, resized, captured, and closed through the long-lived
  compositor owner. `BrowserRenderer.render_html_to_pixels*` and
  `BeRenderResult` retain their existing pixel/capture contract and are not
  treated as display admission evidence.
- **REQ-SURFACE-002 — exact identity:** Every submission, surface, device,
  session, slot, and backing epoch is validated by an opaque runtime receipt.
  Positive integers supplied by a browser producer cannot authorize a surface.
  Local resize uses a surface-backing epoch distinct from physical-device
  generation, so resizing surface A cannot invalidate surface B.
- **REQ-SURFACE-003 — retained resources:** Each child surface owns its
  retained DrawIR/resource revision, per-slot output image or an equivalent
  proven queue dependency, damage history, and release receipts. Resource
  reuse requires compute completion and presenter release for the exact image
  revision. A surface close cannot release another surface's resources.
- **REQ-SURFACE-004 — three receipts:** Submission, compute completion, and
  presenter release are separate typed receipts. Compute completion alone does
  not acknowledge host dirty state. Present acceptance is not physical scanout
  completion; the API promises the documented presenter-release boundary.
- **REQ-SURFACE-005 — ordered publication:** Accepted/submitted/presented
  cursors are distinct. Frames may retire physically out of order, but event
  acknowledgement and visible publication advance only through the contiguous
  frame sequence prefix. Rejected or pending work preserves damage and leases.
- **REQ-SURFACE-006 — event deltas:** Pointer, resource, and timer wakeups are
  coalesced as unsubmitted owner data, then carried with the exact surface,
  device generation, and producer revision. No-damage events allocate or submit
  nothing. A frozen submitted slot cannot be mutated by later events.
- **REQ-SURFACE-007 — lifecycle:** Resize closes only that surface's admission,
  coalesces the newest extent, and rebinds after its leases retire. Device loss
  closes admission for all surfaces on that device, revokes publication
  generations immediately, and retains unresolved ownership until actual
  recovery/teardown evidence. Close, loss, and retirement are idempotent.
- **REQ-SURFACE-008 — compatibility and fallback:** Existing pixel APIs,
  event ordering, and exact pixels remain unchanged. Screenshot/capture is an
  explicit operation and may use a scoped compatibility owner. Fallbacks are
  reported as rejected/pending/terminal outcomes and never as GPU evidence.

## Traceability

| Requirement | Parent requirement | Planned evidence |
|---|---|---|
| REQ-SURFACE-001 | REQ-GPUUI-002, 007, 008 | compositor integration spec; capture/display separation |
| REQ-SURFACE-002 | REQ-GPUUI-003, 004, 005 | wrong-device/slot/epoch receipt matrix |
| REQ-SURFACE-003 | REQ-GPUUI-003, 006 | two-surface isolation and image-retirement tests |
| REQ-SURFACE-004 | REQ-GPUUI-002, 004 | typed receipt and presenter-release tests |
| REQ-SURFACE-005 | REQ-GPUUI-004, 005, 008 | ordered-prefix/out-of-order completion test |
| REQ-SURFACE-006 | REQ-GPUUI-005 | event coalescing and no-damage test |
| REQ-SURFACE-007 | REQ-GPUUI-003, 004, 008 | resize/loss/close integration matrix |
| REQ-SURFACE-008 | REQ-GPUUI-002, 007, 008 | existing pixel contract and fallback gates |

## Explicit non-goals

O2 standalone BrowserSession ownership is not selected. A Simple-only ring,
global cache drain, fabricated receipt, blocking batch, or seed/compiler
artifact cannot satisfy these requirements.
