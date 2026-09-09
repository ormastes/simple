<!-- codex-architecture: Astra review -->
# Browser renderer GPU surface ownership boundary

Status: selected architecture; synchronous source integration under review,
runtime verification and provider admission pending.
Selection: O1 compositor-owned surfaces + B/N2 runtime-owned tunable bounded
submission session. This refines the selected
`simple_2d_web_renderer_gpu_optimization.md` architecture without claiming
completed production integration or hardware evidence.

## Actual production call sites

| Route | Observed owner and operation | Evidence limit |
|---|---|---|
| Pixel browser | `web/browser_session_runtime.spl:BrowserSession.render/render_to_pixels` creates a fresh software `BrowserRenderer` on every call | Renderer fields cannot supply a persistent GPU owner |
| Pixel facade | `gpu/browser_engine/browser_renderer.spl:render_html_to_pixels*` calls `simple_web_engine2d_renderer` or `simple_web_layout_engine2d_fast` free functions | Return value contains pixels; no lease, submit token or present receipt |
| Fast DrawIR | `simple_web_layout_engine2d_fast.spl:_simple_web_layout_render_draw_ir_composition` acquires global bare engine, calls `engine2d_draw_ir_adv_composition_with_images`, parks engine | DrawIR function requests result readback; cache key is backend/extent |
| Upload presenter | `simple_web_html_engine2d_presenter.spl:present_layout_pixels_with_engine2d_readback` uploads host pixels and reads them back | Independent global cache has the same missing surface identity |
| Hosted display | `src/os/compositor/host_compositor_core.spl:render_frame_engine2d` calls `render_draw_ir_composition_resources_window_revision_damaged` | Existing long-lived compositor is the real window owner |
| Device display | `src/os/compositor/compositor_engine2d.spl` calls the DrawIR window-present path, then validates `latest_vulkan_frame_receipt` | Real present and no-readback evidence exists, but completion is synchronous |
| Native boundary | `gpu/engine2d/backend_vulkan.spl:_present_device` flushes compute then invokes `vulkan_sffi_present_buffer[_regions]` | `_flush_pending_compute_impl` uses `vulkan_sffi_submit_and_wait_fence`; no pending frame lease is returned |

All relative library paths in this table are under `src/lib/gc_async_mut/`.
The existing hosted display still constructs image resources from content
pixels. Its no-readback swapchain path alone does not prove that browser layout
and all embedded content were GPU-resident end to end.

`session/session_api.spl` and `graphics_session.spl` are policy/bookkeeping
surfaces: IDs are caller arithmetic and `retain` sets `session_id + 1000`.
`backend_vulkan_adapter.spl` explicitly refuses unbacked init/submit/present.
They cannot be used as device lease authorities. The actual `VulkanSession`
owns retained pipelines/device selection, but does not supply the requested
bounded command-retirement API.

## Canonical owners and transport

For selected O1, the display host owns one device scheduler and a bounded table
of child `GpuRenderSurface` owners. Each surface owns its exact Engine2D target,
retained DrawIR/resource revision, pending damage, frame slots and lifecycle.
The device scheduler holds the sole runtime admission lease; it is not a cache
of unowned engine values. BrowserSession remains a producer and does not own a
standalone display surface.

Browser event processing owns DOM, scene/resource revisions and event order.
It submits copied scalars and frozen DrawIR/resource snapshots. A device token
is an opaque lease name checked by its issuing device owner, not a positive
integer that the browser can manufacture. Actual allocation bytes and release
receipts come from that owner. The existing common GPU contract remains the
location for shared value vocabulary; backend internals stay tree-private.

A surface names an actual output/image owner, not every browser window painted
into a shared compositor target. Those child producers have their own document
and resource generations. The display owner maps accepted producer deltas into
one ordered output sequence; it must not compare unrelated per-document event
counters as if they were one clock. The current common
`GpuRenderSurfaceId.device_generation` also increments on a local resize. A
versioned provider binding therefore needs separate physical-device generation
and surface-backing epoch; resizing A must not invalidate B's device lease.
Keep the legacy field interpretation in its model/compatibility adapter, rather
than silently treating it as a provider-issued device identity.

Candidate public operations (names reserved for a selected implementation):
`gpu_surface_open`, `gpu_surface_offer`, `gpu_surface_poll`,
`gpu_surface_capture`, `gpu_surface_resize`, `gpu_surface_close`.
They return typed ready/pending/rejected/terminal results. `offer` returns queue
acceptance only; `poll` separately reports compute completion, presenter release
and acknowledged event generation. Existing pixel APIs retain their signature.

## Three distinct receipts

1. Submission binds device/session/surface generation, slot generation, frame
   sequence and exact command/resource leases to a backend-issued token.
2. Compute completion proves that exact submission finished. Command scratch
   may retire when its provider proves all references released; the framebuffer
   remains retained while a presenter, capture or later composition reads it.
3. Presenter release proves consumption of the exact image/content revision and
   display target generation. Only then may the surface acknowledge the event
   and reuse image storage. Present acceptance and physical scanout completion
   must be named separately; this API promises the documented release boundary,
   not physical display time.

`GpuRenderSurfaceState` currently models transitions only. Its `complete` takes
caller scalars, `present` constructs a receipt without backend evidence, and
`last_event_generation` advances at `begin`. These are not admission proofs.
The production capsule must validate provider receipts before invoking internal
transitions, maintain separate accepted/submitted/presented generation cursors,
and add explicit abort-before-submit and ordered publication transitions.
Existing model helpers stay source-compatible and cannot be promoted as public
device evidence by a wrapper. Duplicate/stale receipt tests must reach the real
owner validation, not merely repeat the model helper's arguments.

## Frame resources and cache lifetime

Three in-flight command slots do not imply three safe versions of one mutable
framebuffer. A selected implementation must either use three per-slot output
images with per-image damage history, or prove GPU queue dependencies serialize
updates of a retained output with every presentation/capture read. A CPU fence
count and a shared handle are insufficient. Before local damage replay, each
target must have the correct predecessor content revision; otherwise reseed it
from an ordered GPU copy or render the full frame, reporting that work.

Move `_web_fast_engine_slots`, `_web_presenter_engine_slots`, route evidence and
device-dependent route eligibility under the selected owner. Cached engines,
font/image allocations and offscreen children carry surface/device generation
and have one release authority. Immutable pipeline sharing stays with the device
session and uses actual retained references. A surface close releases only its
children. `web_*_engine_cache_drain` remains a legacy process-wide maintenance
operation and is never called by a surface close or resize.

Stateless capture functions may retain a dedicated compatibility owner or use
an explicitly scoped temporary engine. They cannot identify unrelated calls as
the same display surface merely because backend and extent match. Display
admission never uses the compatibility cache or its pixel fingerprints.

## Events, failure and teardown

`GpuPendingEventDamage` remains unsubmitted owner data. Pointer, resource and
timer wakeups reach the semantic owner first, then carry the exact surface and
device generation to `offer`. Ring-full preserves/coalesces pending damage,
performs at most one bounded poll, and returns pending. A frozen slot cannot be
modified by later events. Event acknowledgement follows ordered successful
present release; compute completion alone cannot clear host dirty state.

Resize closes that surface's admission, coalesces the newest requested extent,
and retires only its outstanding leases before releasing extent-dependent
resources and rebinding generation. An exact duplicate completed resize is a
no-op. Shutdown uses the same owner-scoped retirement and is idempotent.

Device loss is distinct from a resize: fences may never signal. Close admission
for all surfaces on that device, revoke publication generations immediately,
retain unresolved allocations in the device recovery owner, and await an actual
device teardown/recovery receipt. A model transition that rejects in-flight
loss cannot implement that protocol alone. Repeated reports for the same loss
generation cannot increment generations repeatedly or release resources twice.
No surface teardown may silently invoke global idle/drain to claim local release.

## Migration gates

1. Implement selected O1 and B/N2. Admit runtime exact retirement, aggregate
   capacity, descriptor immutability and presenter release before connecting any
   production asynchronous submit.
2. Extend the common receipt vocabulary and owner-only transitions; reserve
   distinct generation cursors, pre-submit abort and loss-recovery states.
3. Wrap actual Engine2D/device/presenter resources in the chosen owner. Route
   the existing compositor's DrawIR call through it, maintaining a synchronous
   adapter for current boolean callers until their pending path is migrated.
4. In `host_compositor_core.spl`, move `_mark_external_web_frames_consumed` and
   `dirty.clear` from immediate render success to the exact acknowledged present
   prefix. A rejected frame keeps damage and resource leases available.
5. Connect browser scene/resource snapshots and hosted producer generations to
   that owner. Replace pixel resources on the production GPU path with retained
   DrawIR/device images; explicit screenshot/capture APIs remain compatible.
6. Relocate caches and wire resize, close and device-loss through the same owner.
   Run the linked production test plan before any performance admission.

The original design audit established the missing boundary and real migration
call sites. The synchronous source integration below remains runtime-unverified.

## O1 synchronous provider boundary (PR #520)

The first production slice is now connected at the existing hosted compositor
owner. `CompositorGpuSurfaceOwner` binds one host output surface, separates its
surface-backing epoch from physical device generation, and retains the
immutable DrawIR image-resource snapshot across the real
`Engine2dCompositorBackend -> VulkanBackend -> VulkanFrameReceipt` path. Its
submission, device-fence completion, and present-receipt transitions remain
separate even though the current provider returns them in one synchronous
receipt. The owner snapshots the provider receipt before each call and admits
only a contiguous chain with matching extent, framebuffer, device, swapchain,
submit count, and fence count. Full/idle presentation advances the provider
frame counter once. Damaged DrawIR emits a `device-retained` compute-finalize
receipt first and a `window-swapchain` receipt second; the executor retains
that real intermediate snapshot and the owner validates both consecutive
counters. A two-frame jump without that snapshot remains rejected. Dirty
frames and idle retained-window
re-presents both pass through this owner, so the production loop has no second
unobserved present route. The existing receipt is the only boundary at which
this slice releases its host-side producer snapshot; it is not called a
physical scanout release.

The provider still lacks a distinct presenter-release/scanout receipt and the
Vulkan path still completes compute synchronously. Therefore this integration
does not claim B/N2 asynchronous display submission or physical presenter
release. Ambiguous receipts retain the offered resources and prevent reuse;
the owner never synthesizes a token or completion. Post-invocation failure is
quarantined rather than mislabeled as a pre-submit abort. Quarantine holds at
most one snapshot, limited to 64 resources and 67,108,864 pixels, and blocks
resize, provider replacement, another offer, or close. A future
provider-release operation can replace the synchronous boundary without
changing the owner call-site shape. B/N2 is still not invoked by this slice.
Terminal host paths call `close_gpu_surface`; it succeeds only for an idle
owner. If a provider attempt is quarantined, close reports deferred and the
runtime's provider teardown/quarantine remains the only cleanup authority.

The production resize event reserves an idle provider replacement before
shutting down/recreating the raster executor. A separate monotonic
`provider_generation` authorizes its fresh frame-counter baseline even when
all raw Vulkan handles are reused. Unannounced resets still fail closed;
pending work blocks both the actual replacement call and compositor resize.
The owner uses a distinct submitted state, so a completion cannot bypass
submission observation. This source review admits a WARN development change
only: the current general Simple CLI/check worker and real device execution
remain unavailable, and no runtime or performance PASS is inferred.
