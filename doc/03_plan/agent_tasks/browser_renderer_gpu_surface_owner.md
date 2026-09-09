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
