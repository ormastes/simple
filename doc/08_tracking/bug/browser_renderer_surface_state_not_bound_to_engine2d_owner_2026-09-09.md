# BrowserRenderer surface state is not bound to the Engine2D owner

Status: open; blocks any claim of production BrowserRenderer surface-lifecycle
integration.

## Evidence

- `BrowserRenderer` render methods call pixel-returning free functions. They do
  not receive a backend session lease, submission token, fence completion, or
  present receipt.
- `GpuRenderSurfaceState` and `GpuPendingEventDamage` have no production call
  site in `BrowserRenderer`; their lifecycle was exercised only by a focused
  specification.
- Both web Engine2D caches own module-global bare `Engine2D` slots keyed only
  by backend and extent. They carry no `surface_id` or `device_generation`, so
  a renderer cannot retire or invalidate only resources it owns.
- The current pixel-returning paths include synchronous completion/readback.
  Treating their return as a device-present receipt would fabricate the
  asynchronous ownership evidence required by the surface contract.
- A global cache drain is conservative teardown, not proof that one renderer
  released its resources; it can discard parked resources belonging to other
  surfaces.

The unused BrowserRenderer sidecar fields and lifecycle methods were removed.
The independent surface state machine and its tests remain valid pure-Simple
contracts, including in-flight rejection, generation validation, exact
duplicate-resize stability, and idempotent shutdown.

## Required production boundary

The real renderer/cache route must return an owner-bound session lease and
real backend submission/completion/present evidence. The host event owner can
then freeze generation-bound damage into that surface, submit with the actual
token, retire only a matching fence, acknowledge only after present, and
invalidate per-surface parked resources on resize or device loss. Until those
interfaces exist, no wrapper may synthesize tokens or completion status.

Acceptance requires production call-site coverage for pointer, resource, and
timer wakeups; three frames in flight with bounded backpressure; stale
surface/device rejection; duplicate resize/loss handling; teardown after
retirement; and zero steady-state CPU waits or framebuffer readbacks.

## Astra owner-boundary review

The persistent production display owner exists in
`src/os/compositor/compositor_engine2d.spl`, reached by
`host_compositor_core.spl:render_frame_engine2d` calling
`render_draw_ir_composition_resources_window_revision_damaged`.
It validates real `VulkanFrameReceipt` presentation results. Its compute path
still waits synchronously, so these receipts cannot be converted into pending
async frame tokens. `BrowserSession.render/render_to_pixels` creates a fresh
software `BrowserRenderer` each call; attaching persistent state there would
not migrate this actual display path.

The independent surface model is not a provider authority: `present` takes no
backend receipt and `last_event_generation` advances at `begin`. Production
integration needs separate accepted/submitted/presented generations, exact
provider validation, abort-before-submit, and device-loss recovery while fences
are unresolved. A compute completion alone also cannot release an image still
read by presentation or capture.

The selected O1 owner contract is in
`doc/02_requirements/feature/browser_renderer_gpu_surface_owner.md`.
The recommended O1 follows the existing compositor owner and retains all pixel
APIs as compatibility capture routes. The exact migration, image ownership,
cache scope and acknowledgement boundary are in
`doc/04_architecture/browser_renderer_gpu_surface_owner.md`, with production
tests in `doc/03_plan/sys_test/browser_renderer_gpu_surface_owner.md`.
No new public API or pending Vulkan runtime option was auto-selected. No source
implementation or device verification is claimed by this review.
