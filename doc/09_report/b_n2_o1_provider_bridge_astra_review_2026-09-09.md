# B/N2 to O1 provider bridge review

STATUS: FAIL for the proposed connection; the uncommitted bridge was removed.
The selected O1 compositor owner and B/N2 runtime session remain the target.
The existing committed synchronous O1 adapter and standalone B/N2 provider
remain unchanged. This report does not admit either as an asynchronous display
implementation.

## Decision and recoverability

After two Sol reviews, Astra inspected the actual provider, font, child-surface,
and presenter call paths. Connecting them correctly requires coordinated owner
and provider interfaces, not a change to the submission helper's return timing.
The eight-file bridge was removed before publication. Its complete pre-removal
diff, including Sol's fixes, is retained locally at
`build/bridge-review/b_n2_o1_rejected_bridge.patch`.

Sol's inert-session construction and descriptor/source handle revocation fixes
were correct within that attempted connection. Both depended entirely on the
removed async backend state; retaining those branches would leave unused code.
Existing committed runtime ownership and handle-release behavior is preserved.

## Concrete failures

| Boundary | Observed behavior | Consequence |
|---|---|---|
| Session authority | `rt_vulkan_async_session_create_with_wait` admits one session and rejects any existing direct-compute owner. `Engine2D.create_shared_vulkan_offscreen` calls `enable_frame_batching` for every shared child. | Opening a session from each backend makes the first backend exclude the others; the rejected children then attempt forbidden legacy compute. |
| Presentation wait | `_async_wait_for_present` called `vulkan_sffi_wait_idle`; `rt_vulkan_wait_idle` returns zero whenever an async session is active. | The first pending async frame fails its completion step. Removing that rejection would violate the selected no-normal-path-idle requirement. |
| Recording/resource gate | Primitive recording still calls legacy quarantine reap; `rt_vulkan_bind_buffer` rejects any nonempty `quarantined_compute`, including known async submissions. | A later slot cannot bind independent fresh resources while an earlier slot is pending. Merely reserving three empty commands does not prove a working ring. |
| Mutable font resources | `backend_vulkan_font.spl` indexes warm descriptor/parameter pools using the current pending array length. The bridge cleared those arrays on submit. | The next batch can overwrite parameters or mutate descriptors still read by an earlier submission. Retaining an `Arc` prevents destruction, not concurrent mutation. |
| Dispatch dependency | `_bitmap_text_bg_atlas_path` explicitly relies on synchronous `_flush_pending_compute` completion between the background rectangle and glyph read/modify/write. | Changing flush to enqueue removes the existing dependency proof; queue order alone is not a replacement memory barrier. |
| Receipt boundary | The host still consumes a boolean operation and `VulkanFrameReceipt`; the bridge exported local counters as a binding observation. | Pending, rejection, compute completion, and physical presenter release cannot be represented or independently proven. Counters cannot authorize resource reuse. |
| Terminal ownership | Backend shutdown called the failing async present wait before reaching legacy recovery. It never used the B/N2 `recover`/`abandon_device` path. | Unknown completion can leave the only reachable owner stuck without a usable terminal operation. |
| Pressure policy | On `WOULD_BLOCK`, the bridge called `acquire` again after local reaping. Each provider acquire may already perform one configured bounded wait. | One offer can perform two pressure waits instead of the selected maximum of one. |

Source owners are `src/compiler_rust/runtime/src/vulkan_graphics_runtime_*`,
`src/lib/gc_async_mut/gpu/engine2d/{engine,backend_vulkan,backend_vulkan_helpers,backend_vulkan_font}.spl`,
and `src/os/compositor/{compositor_engine2d,compositor_gpu_surface_owner,host_compositor_core}.spl`.
The current selected requirements are
`doc/02_requirements/feature/browser_renderer_gpu_surface_owner.md` and
`doc/02_requirements/feature/vulkan_async_compute_submission_ring.md`.

## Ordered implementation packages

1. **Provider resource admission — Sol, then Astra review.** Distinguish an
   exact known async submission from completion-unknown quarantine before
   admitting new recording. Reject descriptor mutation whenever that descriptor
   is retained by recording/submitted work. Apply the same retained-resource
   rule to host writes and other descriptor update entrypoints; unknown ranges
   overlap. Public token revocation may retain physical `Arc` ownership. Verify
   the actual resource entrypoints through an injected provider: submit slot A,
   bind and record independent slot B, reject A's descriptor/parameter mutation,
   preserve unknown-completion rejection, retire A exactly once, and then permit
   its resource reuse. Empty-command session tests cannot close this package.
2. **One compositor device scheduler — Sol after interface review.** Put the
   single B/N2 owner on the long-lived device scheduler. Shared offscreen
   backends receive non-owning, generation-checked recording leases, never their
   own session or permission to close the device. All primitive, image, font,
   direct-compute, and child-surface operations must enter that authority or
   reject before mutation. Test two surfaces with one session and one aggregate
   3/8/16 capacity; closing or resizing A cannot drain B or invalidate its lease.
3. **Slot-local immutable work — Sol after scheduler contract freeze.** Tie
   parameter/descriptor pools and output image revisions to exact slot
   generations. Retain atlas/resource revisions until every reader retires.
   Express compute write/read dependencies with validated barriers or queue
   dependencies. Test rectangle-to-glyph, image composition, atlas replacement,
   same-slot reuse, and interleaved surface work. Three submitted frames must
   keep independent mutable resources; exact pixels must match synchronous
   output before any performance claim.
4. **Pending and presenter receipt path — Sol after provider interface review.**
   Carry explicit accepted/pending/rejected/unknown outcomes through Engine2D,
   the presenter, and O1. Poll exact compute tokens; enqueue a present only when
   its dependency is satisfied. Add a provider-defined presenter-release
   receipt for the exact image revision. Keep compute retirement, resource
   release, and dirty-state acknowledgement separate. Reuse images only after
   all required releases and publish only the contiguous frame prefix. Count
   at most one N2 bounded pressure wait per offer; return pending to the event
   loop instead of retrying inside the boolean adapter.
5. **Device loss, cancellation, and shutdown — Sol, Astra final review.** The
   central owner closes admission and revokes publication generations first.
   Drain proven completions, use one explicit B/N2 recovery when necessary,
   and retain failed-recovery ownership through `abandon_device`. Its result
   `QUARANTINED=2` is terminal retained ownership, not completion or resource
   release; the current provider requires process restart. Test pending close,
   loss during present, wrong-generation callbacks, repeated close, and failure
   between compute completion and presenter release.

Packages 1 and the interface design for 2/4 can proceed independently. Package
3 depends on the scheduler lease shape; production connection requires all five.
No change may enable B/N2 merely because the optional provider symbols exist.
The capability claim must cover the actual recording, resource, presenter, and
terminal paths used by the compositor.

## Verification and publication

The removal is checked against the pre-bridge Git base for all eight files.
The rejected source-presence test is removed with the connection: finding
`submit`, `poll`, and `retire` strings did not prove their provider compatibility.
No runtime, hardware, performance, or SPipe manual acceptance is claimed by this
review. Previously passing runtime tests are not rerun because no runtime source
changes are retained.

Commit recommendation: commit this review and the linked task-plan update only.
Do not publish the rejected patch. Keep the PR's B/N2 connection and physical
presenter-release gates explicitly pending. Admission still requires a current
Simple/provider build, complete live 3/8/16 recycling/ownership coverage, and
matched C/Simple and Chrome/Simple rendering evidence.
