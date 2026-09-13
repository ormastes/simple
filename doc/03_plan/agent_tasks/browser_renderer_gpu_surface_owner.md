<!-- codex-architecture -->
# Browser GPU owner agent lanes

Status: selected O1 + B/N2; implementation depends on runtime/provider
admission.

| Lane | Owner | Scope |
|---|---|---|
| Design/escalation | Astra (`astra_browser_renderer_owner`) | Real call graph, ownership/receipt boundary, options and test plan |
| Common owner | Sol | Shared receipt extensions and bounded owner transitions; no runtime token synthesis |
| Display adapter | Sol after provider admission | Existing compositor call sites, ordered acknowledgement, surface-local teardown |
| Browser producer/cache | Sol after adapter interface freeze | Generation-bound scene/resource events, compatibility captures, cache ownership |
| Runtime/provider | Existing runtime lane after explicit pair selection | Exact retirement, aggregate capacity and presenter-release capabilities |
| Merge owner | Root coordinator | Preserve concurrent work, sequence dependencies, collect exact evidence |
| Final reviewer | Astra | Reject sidecar-only integration, cross-surface drain and unproven GPU claims |

Shared interface names and manual/setup/checker helpers are fixed in
`doc/04_architecture/browser_renderer_gpu_surface_owner.md` and
`doc/03_plan/sys_test/browser_renderer_gpu_surface_owner.md` before sidecars
start. The selected O1 owner and B/N2 session are the only implementation
target; O2, A/N1, and blocking-only alternatives are not implementation lanes.

## B/N2 connection order after provider review

The attempted backend-local connection was removed after two Sol reviews and
Astra's provider review. Follow the ordered packages and concrete acceptance
cases in
[B/N2 to O1 provider bridge review](../../09_report/b_n2_o1_provider_bridge_astra_review_2026-09-09.md).
Start with the actual descriptor/buffer admission entrypoints and the central
compositor scheduler contract. Then implement slot-local resource lifetimes,
explicit pending/presenter-release receipts, and central recovery/teardown.
All shared offscreen children must borrow the one device scheduler; enabling
frame batching cannot open a competing session. A source-presence test or
empty-command ring test cannot admit the connection.

## Astra scheduler escalation

The later five-file host scheduler candidate was also removed after its second
Sol review: it had no production recording/presenter callers and opened a new
session from an unrelated completed receipt. The exact removal and recovery
record is
[Host scheduler review](../../09_report/host_compositor_gpu_scheduler_package_2026-09-09.md).
The selected architecture now freezes `GpuAsyncDevicePortV2`, the shared
session/recording identities, and the actual hosted offer/poll/acknowledgement
chain. Read **Provider port required before production connection** before
assigning another implementation lane. A new wrapper around
`VulkanAsyncSubmissionSession.open_with_wait` is not the next package.

The Pure Simple owner/DrawIR/event path remains the production lane; Rust is
background provider/reference work. Sol implements the missing port consumers
only with actual provider authority, then Astra reviews the full chain.
Preserve the reserved SPipe helpers in the linked test plan. Do not publish
async support or performance claims from source-only/injected-port checks.

## V2 escalation implementation sequence

Astra removed the subsequent four-file V2 model after two Sol cycles. The
[V2 review](../../09_report/gpu_async_device_port_v2_astra_review_2026-09-09.md)
is the next handoff, with actual code paths, native authority requirements and
the recoverable candidate location. It also records the newly found
[canonical buffer-binding export gap](../../08_tracking/bug/vulkan_async_bind_buffer_export_gap_2026-09-09.md).

1. Sol: repair that export gap with explicit unsupported behavior unless the
   checked operation is actually implemented. No legacy-binder substitution.
2. Sol: implement the actual context-admission adapter at VulkanSession/SFFI
   and a real Engine2D initialization consumer together.
3. Sol: migrate primitive/font/image DrawIR into exact recording leases and
   bounded slot resources under that same owner.
4. Sol: implement presenter release, then connect hosted offer/poll, retained
   presentation, damage and input acknowledgements as one production chain.
5. Astra: review provider-derived authority, two-surface lifetime isolation and
   real production-path evidence before Root commits/pushes that package.

No new sidecar owns a parallel scheduler or foreign-policy implementation.
Rust remains background/reference work. Keep each new implementation file
below 800 lines. The shared helpers in the existing system test plan remain
reserved; no value-fixture test substitutes for their real provider path.
