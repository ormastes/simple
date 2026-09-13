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

### Damage retained across a delayed present

The host asks `DirtyRegion` for one owner-issued prefix value containing its
epoch and rectangle count before provider entry. Appending a later
pointer/resource/timer invalidation does not change that epoch. After validating
the exact provider/presenter and external frame receipts, the host retires only
the captured prefix, preserving later
rectangles even if they overlap the older damage. Clear and successful prefix
retirement advance the epoch; clear-and-readd with identical rectangles and
duplicate acknowledgement cannot consume the replacement damage. A count not
issued for the active epoch is rejected rather than retiring an arbitrary
shorter prefix. Epoch exhaustion rejects capture instead of wrapping. The
checkpoint is held by the
host owner and grants no device authority.

This replaces the earlier rectangle-count identity check and whole-set clear
in the typed present path. It is a production-connected prerequisite for
REQ-SURFACE-005/006, not an async provider implementation. The software
HostCompositor-path regression supplies presenter observations as test data;
live provider release and Vulkan async admission remain pending. See the
[damage checkpoint report](../09_report/host_present_damage_checkpoint_2026-09-10.md).

## Provider port required before production connection

Astra's scheduler escalation removed the unused host scheduler candidate after
two Sol cycles. See
[the exact review and recovery record](../09_report/host_compositor_gpu_scheduler_package_2026-09-09.md).
This section freezes the next implementation boundary. The names below are
reserved design names; no implementation, native symbol, or hardware support
is claimed by declaring them here.

The long-lived Pure Simple device owner must acquire its admission from the
**same live VulkanSession that owns the Engine2D pipeline and output resources**.
The existing `VulkanAsyncSubmissionSession.open_with_wait(capacity, timeout)`
cannot supply that contract: it has no expected-device/session/swapchain
arguments, and its returned opaque handle identifies a separately created
global provider owner. A completed `VulkanFrameReceipt` can observe a previous
frame; it cannot grant the new owner's authority. Do not construct a second
session and then compare local counters or positive handle fields.

Keep scheduling, surface tables, resource versions, pending damage, and event
publication in `.spl`. The backend port supplies opaque device operations and
their actual results. The Rust provider may serve as background/reference
evidence, but moving policy into Rust does not implement the selected Pure
Simple compositor. A provider advertised as usable must implement the whole
binding, recording, presenter, and terminal contract, not just export the
existing optional B/N2 symbols.

The private port is `GpuAsyncDevicePortV2`, held only by the device owner.
Shared copied vocabulary belongs beside the existing contracts in
`src/lib/common/gpu/render_surface_contract.spl` (or its versioned child), not
in a parallel scheduler type system. Preserve the existing V1 layouts.

| Reserved value/operation | Required authority and result |
|---|---|
| `GpuDeviceBindingV2`; `bind_existing_session` | Provider validates the exact existing device/session and output target, rejects live legacy recording and a competing admission owner atomically, and returns an opaque owner binding with device generation, session generation, and binding generation. Failure leaves the old owner usable. Raw pointer equality and locally incremented generations are insufficient. |
| `GpuRecordingLeaseV2`; `borrow_surface` / `acquire` | Provider binds a non-owning surface lease to that owner and the actual framebuffer/image allocation. Every recording token resolves to the exact device/session/binding, surface epoch, slot generation, and output revision. The host supplies producer/event revision data; these fields never confer native authority. Children receive no cancel-session, recover, abandon, or close-device operation. |
| `bind_resources` / `record` | Exact token plus checked descriptor, pipeline, buffer range/access, image revision, and dependency inputs. Provider validates membership and lifetimes before mutation. The returned command is used to record actual DrawIR primitives/images/fonts; retrieving a command alone is not recording. Unknown range/access information overlaps. |
| `submit` / `poll_compute` / `retire_compute` | Returns rejected-before-submit, accepted/pending, exact compute completion, or completion-unknown. A receipt carries the same immutable binding and opaque token. Retiring command scratch does not release an output image that present/capture/another composition still reads. |
| `enqueue_present` / `poll_present_release` | Binds the exact output image revision, compute dependency, display target generation, and provider-issued present token. Acceptance, completion, and source-image release are distinct. A copy-completion fence may prove release of its source buffer if that is the provider's defined boundary; it cannot claim swapchain/scanout release. |
| `GpuFrameProgressV2` | Carries typed rejected/pending/unknown/complete states and the separately validated submit, compute, and image-release facts. The Pure Simple owner adds its accepted/submitted/acknowledged output sequence and per-producer revision mapping only after receipt validation. No caller-set proof booleans. |
| `release_surface` / `recover` / `abandon` | Provider authorizes exact surface cleanup or device terminal ownership. Surface cleanup cannot close the session or drain another surface. Device recovery belongs solely to the central owner; quarantined abandonment is retained ownership, not completion. |

Opaque records are looked up and validated by their issuing owner on every
operation. Copying a lease does not clone its authority or grant teardown.
Revocation must invalidate all copies; generations cannot wrap. A capability
probe and later use must still validate the binding on the actual operation,
so device replacement between those calls cannot authorize stale work.
No production adapter may turn an injected test port into a device proof.

### Actual owner and event call chain to migrate together

1. `src/os/hosted/hosted_entry.spl` offers its pending semantic snapshot to
   `HostCompositor.gpu_surface_offer` and polls `gpu_surface_poll` on later
   event turns. These are the already-reserved public operations. Pending
   does not enter compatibility rendering or stop evidence mode.
2. `HostCompositor` freezes that offer's producer revisions, damage and
   resources. Its single device owner holds the provider binding and all
   child surface leases. `Engine2D.create_shared_vulkan_offscreen` borrows
   through that owner; it cannot call `enable_frame_batching` to create a
   legacy command behind an active session. The same rule covers font,
   image, primitive, direct-compute, and retained-window routes.
3. `Engine2dCompositorBackend` records the composition through the exact lease
   into per-slot immutable descriptor/parameter storage and a versioned output
   image. `backend_vulkan_helpers._flush_pending_compute_impl` must gain the
   real token-based path and preserve explicit write/read dependencies; the
   synchronous `submit_and_wait_fence` path cannot be relabeled as async.
4. The central owner submits once and polls exact compute progress on later
   turns. When the provider dependency is satisfied, it enqueues the exact
   present and retains the image until the defined release receipt. Device
   completion, command retirement, present acceptance, and image release stay
   separate even if a provider reports some together.
5. Only the contiguous released output prefix commits presentation. At that
   commit, acknowledge the frozen producer revisions through
   `_mark_external_web_frames_consumed`, consume only the damage belonging to
   that prefix, and emit the corresponding input presentation receipt.
   New damage received after submission remains pending; blindly calling
   `dirty.clear()` would discard it. In `hosted_entry.spl`, advance
   `presented_event_id` and `presented_mutation_revision` from that receipt,
   never from the boolean return or the newest current input receipt.

The old boolean `render_frame_engine2d` contract means synchronously complete
or rejected. It cannot encode an accepted pending frame. Preserve that meaning
for compatibility callers while migrating the production hosted loop to the
typed operations in one reviewable change. Likewise, the idle retained-window
path must poll/present through the same owner rather than silently using its
old synchronous present beside in-flight work.

N2 admission calls the provider acquire operation at most once per offered
frame, including when the local table appears full. That operation owns its
single configured bounded pressure observation. A local early capacity return
must not silently change N2 into a no-wait policy, and a failed acquire must
not be retried internally. Recycle records in bounded tables; retaining every
retired lease or closed surface forever defeats the memory bound.

Use the shared 3–16 capacity and timeout validators already present in the
common contract. Capacity covers all child surfaces together. Slot images
must carry their actual predecessor content revisions before damaged replay;
reusing a different ring image requires an ordered GPU seed/copy or an honest
full redraw. Retain font atlas and parameter revisions until their last reader
retires, including the background-rectangle-to-glyph dependency.

### Acceptance of this port and production connection

Extend the existing production test plan with its reserved
`open_browser_surface_pair`, `assert_surface_owner_receipts`, and manual step
names. Tests must enter the real hosted offer/poll path and observe operations
at the actual port; a zero-caller facade or an empty-command session cannot
pass. An injected port proves control flow only and is labeled accordingly.

- Two surfaces share exactly one provider binding and aggregate capacity at
  3, 8, and 16. Recording real DrawIR B while A is submitted succeeds only for
  legal resource access. A's resize/close does not wait for or invalidate B.
- Wrong session/binding/device/surface/slot generations fail before mutation;
  handle reuse, copied stale leases, provider replacement, duplicate receipts,
  and a forged positive scalar record cannot advance owner state.
- Three distinct output revisions remain alive concurrently. A rectangle,
  glyph, and image composition have correct barriers and immutable parameters;
  controlled post-timing captures match synchronous output exactly.
- Out-of-order compute completion does not acknowledge events. Hold a present
  release, inject a newer pointer/resource/timer event, and verify both the
  old image lease and the new pending damage remain. Release the contiguous
  prefix and verify only its exact revisions are consumed and acknowledged.
- Full capacity performs at most one N2 pressure wait per offer; later event
  turns reclaim exact released slots. Repeated recycling leaves bounded
  record count, retained bytes, descriptors and allocations. Normal operation
  has no device-idle call, full-frame readback, or hidden retry loop.
- Pre-submit rejection, ambiguous submit, loss between compute and present,
  failed recovery, abandonment, and repeated close preserve the exact owner
  and cannot manufacture image release or event acknowledgement.

The source review/removal does not satisfy these cases. Keep the production
async and performance gates pending until an admitted Pure Simple runtime and
actual provider execute them. Do not reopen the same five-file facade task;
start at this missing port and include its production consumers.

### V2 implementation escalation: concrete missing boundary

The four-file V2 candidate also failed after two Sol cycles. Astra removed it:
it had no provider implementation or production consumer, its session
capability accepted caller-supplied identity, and its recording packet carried
metadata without actual DrawIR commands. The current committed managed-buffer
facade additionally imports a missing canonical SFFI operation. These are
implementation defects, not unavailable-runtime evidence gates.

The [Astra V2 review](../09_report/gpu_async_device_port_v2_astra_review_2026-09-09.md)
defines the minimum real context admission, scoped recording, compute and
presenter operations, with source paths and an ordered implementation handoff.
Start with the canonical export gap and actual VulkanSession/provider boundary;
do not recreate the removed trait/owner/value-test package. Scheduling, DrawIR
policy and event publication remain Pure Simple. O1 + B/N2 is still selected,
and none of its pending production or hardware gates is waived.
