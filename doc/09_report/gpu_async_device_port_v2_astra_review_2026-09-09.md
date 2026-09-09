<!-- codex-architecture -->
# GPU async device port V2: Astra escalation

Status: **FAIL for the implementation candidate; WARN for this removal and
implementation handoff.** Reviewed against PR worktree HEAD
`e5e4b75cfa2b8d8f325d0fa4bdad647df62b03f9`. The selected O1 + B/N2 production
goal remains incomplete. No runtime, GPU, SPipe, or performance PASS is claimed.

After two Sol cycles, the four uncommitted candidate files still had no
provider implementation or production consumer. Astra removed them instead of
publishing a second unused owner model. The existing synchronous O1 owner and
committed standalone B/N2 facade are unchanged.

## Decisive source evidence

| Current source | Observed boundary and consequence |
|---|---|
| Rejected owner, `GpuAsyncSessionCapabilityV2.from_live_session` | Accepted any positive caller-supplied `session_identity` after `is_open()`. The latter only tests that the facade's handle is positive. This proves neither live provider membership nor equality with the Engine2D session. |
| Rejected `GpuAsyncDeviceProviderV2` | No implementation exists. `GpuAsyncDevicePortV2` has no production constructor caller. The restricted capability did not expose acquire or recording, so an adapter could not perform those operations through that capability. |
| Rejected `GpuDrawIrRecordingPacketV2` | Contains resources, dependencies and revisions but no actual DrawIR commands, primitive parameters, glyph runs or image composition payload. A positive fingerprint cannot prove recording. |
| Rejected unit spec | Imports only the common value module and tests synthetic records. It never constructs the device owner, calls a provider, submits DrawIR, or enters the hosted event path. |
| `src/lib/gc_async_mut/gpu/engine2d/vulkan_session.spl` | `VulkanSession` owns shared pipeline handles, but queue/pool fields are runtime-managed placeholders. Its `generation` is local. Command creation uses the global SFFI provider. No backend-issued context export binds these objects to an async owner. |
| `src/lib/gc_async_mut/gpu/engine2d/vulkan_async_submission.spl` | `open_with_wait` takes only capacity/timeout, and `is_open` checks a local positive handle. Its called buffer-binding facade is missing from the canonical SFFI owner at this HEAD; see the linked bug. |
| `src/compiler_rust/runtime/src/vulkan_graphics_runtime_async_offer.rs` | Background/reference implementation creates a ring on the current global device, rejects direct commands/quarantine, and returns an opaque ring handle. It does not validate an expected Engine2D context, resource set or display binding supplied by the caller. This inspection does not propose a Rust production fix. |
| `src/lib/gc_async_mut/gpu/engine2d/engine.spl` | `create_shared_vulkan_offscreen` borrows the existing session, enables legacy frame batching and clears the child. Attaching the ring beside this path creates competing recording authority. |
| `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl` | `_enqueue_framebuffer_compute` and `_enqueue_image_composite` bind real descriptors and issue dispatches using legacy command handles. `_flush_pending_compute_impl` calls `submit_and_wait_fence`, then observes/frees the fence and descriptors. Its result cannot be recast as accepted/pending. |
| `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl` | `_present_device` flushes compute, calls `vulkan_sffi_present_buffer[_regions]`, then updates synchronous frame fields. The scalar return is not a separately pollable presenter/source-release token. |
| `src/os/compositor/host_compositor_core.spl` | `render_frame_engine2d` immediately consumes external frames and clears dirty state after synchronous success. There is no public typed `gpu_surface_offer`/`gpu_surface_poll` implementation. |
| `src/os/hosted/hosted_entry.spl` | Boolean false invokes compatibility rendering or stops evidence mode; true advances the newest input receipt. Neither result can represent accepted pending work without changing this caller. |

The owner file was also 932 lines, over the 800-line architectural limit.
Splitting it would cure that size defect but leave the authority and production
integration failures intact.

The apparent Pure Simple alternative
`src/lib/nogc_async_mut/gpu/vulkan_icd_sffi.spl` is not an admitted replacement:
its queue submit/present methods return `device_handle > 0`, and instance/device
construction increments local counters after a library-file existence probe.
The 3D `vulkan_commands.spl` is a command data model. Neither supplies real
native context membership, asynchronous completion, or presenter release.

## Minimal missing Pure Simple/SFFI boundary

Keep the public names and ownership choices in the existing
[architecture](../04_architecture/browser_renderer_gpu_surface_owner.md).
This section specifies backend facts required to implement them, not a new
alternative or an implemented ABI. Preserve V1 layouts. New entrypoint names,
wire version and layouts must be frozen with the actual backend implementation
before adding declarations or a capability advertisement.

Pure Simple owns the long-lived device controller, bounded surface/slot tables,
resource revisions, DrawIR lowering/recording order, pending damage and event
publication. Native Vulkan operations use the canonical no-GC sync SFFI owner;
compatibility families re-export it. Driver calls and real object-lifetime
observations belong at that boundary. A Rust owner/scheduler remains reference
work and cannot count as this Pure Simple implementation.

The current opaque native resource registry cannot be imported safely by
copying scalar handles. Its owner must expose a checked binding transaction,
or the Pure Simple backend must create and own the actual Vulkan context and
resources through driver SFFI from initialization onward. The latter is a
real backend migration, not a cast between the existing handle namespaces.
In either implementation, the following operations need real authority:

1. **Export/admit the existing context.** The backend returns a revocable
   opaque capability for the exact live device, Engine2D resource session and
   display target. Admission checks competing legacy recording and actual
   resource membership atomically; failure preserves the old owner. Expected
   identities are validation inputs, never caller-created proof. Every later
   operation resolves the capability in the same owner and detects replaced
   devices, stale resource handles and revoked copies.
2. **Acquire a surface recording lease.** Bind the real output allocation and
   surface generation under that context. Return an opaque token for a fresh
   slot generation, with aggregate capacity 3–16 and the selected timeout.
   Exactly one provider acquire/pressure observation is allowed per offer.
   Surface loans cannot close, cancel or recover the device owner.
3. **Bind and record through that token.** Validate buffer range/access,
   descriptor membership, immutable pipeline use and retained image/font
   revisions before mutation. Record real DrawIR-dispatched commands using
   immutable per-slot descriptor/parameter storage. Keep command handles
   private to the backend; future operations must revalidate the token instead
   of accepting a recycled raw handle. Unknown ranges/access overlap. The
   checked buffer-binding operation itself is currently missing at this HEAD.
4. **Submit, observe, retire exact compute.** Return rejected-before-submit,
   accepted/pending, completed, or completion-unknown from the real queue/fence
   result. Command/descriptor retirement must not release an output allocation
   that a presenter, capture, or another composition still reads. An ambiguous
   operation retains its resource graph and blocks reuse.
5. **Present and observe source release.** Enqueue the exact output revision
   with its real compute dependency and target generation; return an opaque
   present token. Observe acceptance, presentation completion as defined by
   the provider, and release of the source allocation as separate facts. A
   transfer fence may release its copied source; it does not prove swapchain
   image release or physical scanout. A synchronous positive status cannot
   synthesize any of these pending receipts.
6. **Abort, release and recover.** Pre-submit abort releases only its exact
   recording lease. Surface release cannot drain siblings. The central owner
   alone handles device recovery/abandonment; unknown completion retains
   ownership without a false release receipt. Generation exhaustion rejects
   admission instead of wrapping. All registries recycle within fixed bounds.

This boundary is missing functionality, not merely missing test tooling.
Adding a trait, forwarding to `open_with_wait`, or substituting
`submit_no_wait` inside the old flush cannot implement it. In particular,
legacy `submit_no_wait` places commands in provider quarantine and does not
provide the selected shared-surface resource/presenter lifetime contract.

## Ordered implementation handoff

1. Repair the source/SFFI export mismatch in the linked bug as a bounded
   Pure Simple task. Without an implemented checked provider operation, expose
   explicit unsupported status; never redirect managed binding to the legacy
   unscoped binder. This repairs source honesty, not async capability.
2. Implement context admission at the real VulkanSession creation/resource
   owner and its canonical SFFI boundary. Supply the actual provider adapter
   and one real Engine2D constructor consumer in the same package. Verify
   wrong-device, competing legacy recording and revoked-copy rejection at
   the mutation boundary. A new unused model package is not an increment.
3. Migrate actual primitive, glyph and image recording to scoped leases.
   `create_shared_vulkan_offscreen`, font/direct compute and composition must
   use the same owner. Retain per-slot outputs and immutable inputs; damaged
   replay on a different output slot requires a proven predecessor GPU copy
   or a full redraw. Record write/read barriers, including background-to-glyph
   dependencies. Do not release image resources at compute retirement alone.
4. Implement the real presenter token/release operations. Then connect
   `HostCompositor.gpu_surface_offer/gpu_surface_poll`, Engine2D compositor
   recording, retained idle presentation and `hosted_entry.spl` together.
   Freeze producer revisions when offered, retain newer damage, and commit
   only the contiguous validated output prefix. Advance hosted input receipt
   fields from that committed snapshot, never the newest current event.
5. Execute the existing
   [surface-owner test plan](../03_plan/sys_test/browser_renderer_gpu_surface_owner.md)
   once with an admitted Pure Simple runtime/provider: two surfaces at
   capacities 3/8/16, real rectangle/glyph/image DrawIR, forced delayed release,
   ring reuse, resize, loss and surface-local close. Only then collect no-idle,
   wait/readback/allocation counters and controlled pixel captures. C/Vulkan
   and Chrome comparisons remain separately unadmitted until those real
   production paths and the canonical Chrome library build are available.

Use Sol for each bounded implementation and initial review; escalate the same
failure after two cycles to Astra. Root owns merge/push and final scope checks.
Keep new owner/contracts/recording/presentation files below 800 lines with
shared values in `common`; splitting modules must not create competing owners.
Preserve the existing reserved SPipe `step(...)`, setup and checker names.

## Recovery and verification scope

The removed untracked candidate is recoverable under the ignored directory
`build/bridge-review/gpu-port-v2-rejected.qEpSLtjX/`: `common.spl`, `owner.spl`,
`spec.spl` and `guide.md` preserve the exact four files. They are investigation
artifacts and are excluded from the commit set.

Removal/link/whitespace checks are source-only. No compiler, unavailable check
worker, full bootstrap, device test, or previously-green suite was rerun.
The production goal remains pending, not PASS. The associated source defect is
[the managed buffer-binding export gap](../08_tracking/bug/vulkan_async_bind_buffer_export_gap_2026-09-09.md).
