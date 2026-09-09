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

## O1 vertical slice landed on PR #520

`src/os/compositor/compositor_gpu_surface_owner.spl` now binds the actual
`HostCompositor.render_frame_engine2d` window-present route and the production
idle `HostCompositor.represent_retained_engine2d` route to one
compositor-owned output capsule. The capsule keeps separate local
`surface_epoch` and physical `device_generation` cursors, retains the copied
DrawIR image-resource snapshot from offer through the provider's exact
`VulkanFrameReceipt`, and validates submission, device-fence completion, and
present completion as distinct owner transitions. The host call path is:

```text
HostCompositor.render_frame_engine2d
  -> Engine2dCompositorBackend.render_draw_ir_composition_resources_window_revision_damaged
  -> Engine2D/VulkanBackend.present_window_device
  -> latest VulkanFrameReceipt
  -> compositor owner receipt validation and resource release
```

Each call begins from the provider's exact prior receipt and accepts only its
next receipt chain with unchanged dimensions/framebuffer/device/swapchain identity and
monotonic submit/fence evidence. Device replacement advances its own
generation; resize/backing replacement advances the surface epoch. A provider
frame reset with reused raw handles fails closed, preventing ABA acceptance.

The release boundary is explicitly named `synchronous-present-receipt`. The
current provider has no distinct presenter-release/scanout receipt, so this
slice does not claim asynchronous present release or physical scanout
completion. An incomplete or ambiguous receipt quarantines at most one
bounded resource snapshot (64 resources, 67,108,864 pixels) and blocks reuse,
resize, replacement, or close; no synthetic token or success is generated.
Only an explicitly pre-invocation offer may use `abort_offer`; a failed or
missing post-invocation receipt never does. B/N2 remains unconnected. The
terminal hosted paths attempt owner close before Engine2D shutdown; pending
work refuses close and remains bounded rather than fabricating provider
release. The focused owner contract is
`test/01_unit/os/compositor/compositor_gpu_surface_owner_spec.spl`.

## Astra review corrections to the synchronous integration

The first synthetic fixture omitted a real provider transition:
`engine2d_draw_ir_render_composition_damaged_with_images` calls
`finalize_compute_frame_no_readback` before the compositor calls
`present_window_device`. Both advance `VulkanBackend.frame_index`. Requiring
only `prior + 1` would quarantine a valid damaged frame. The executor now
retains the actual intermediate receipt; owner validation accepts each exact
next counter in turn, requires completed device-retained/no-readback semantics
for the intermediate, and rejects a bare `prior + 2` jump or counter rollback.

The host resize event previously bypassed the new owner and could destroy its
executor. It now reserves an idle provider replacement before that operation.
The explicit provider generation admits a fresh receipt baseline even when
the allocator reuses every raw handle. Pending work rejects the real resize
and replacement paths, and the event loop exits before additional rendering
after a rejected replacement. A separate submitted state also prevents direct
completion/presentation from skipping submission observation.

The focused owner specification now has 20 scenarios, including damaged then
idle presentation, missing/duplicate intermediates, counter regression,
out-of-order completion, raw-handle reuse, generation exhaustion, unbound
offers, intermediate target mismatch, contradictory host-cache refresh, and
resource-capacity rejection. The
source adoption fixture names the actual damaged-render method and checks
production receipt/replacement wiring. These are unexecuted specifications at
this revision, not runtime PASS evidence. Source review and whitespace checks
are sufficient only for a WARN development PR; full production verification,
SPipe generation, device lifecycle evidence, and B/N2 integration remain open.
