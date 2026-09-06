# System Test Plan — Web Renderer Vulkan 4K Showcase Hardening

| Requirement | Scenario evidence |
|---|---|
| REQ-WEB4K-001/002 | Inventory validates; generated showcase covers every row; deliberate missing/false owner fails. |
| REQ-WEB4K-003 | Initial tab, pointer, Arrow/Home/End, Enter/Space, focus and selected panel transitions. |
| REQ-WEB4K-004/005 | 3840×2160 strict Vulkan cold/warm receipts; software/fallback/stale/malformed rows fail. |
| REQ-WEB4K-006/007 | Real Chrome receipt plus exact tab-set and image comparison; missing/mismatched rows fail. |
| REQ-WEB4K-008 | Existing renderer/Draw IR/Engine2D/backend and runtime-boundary gates remain green. |

Primary manual flow uses: `Open the Vulkan 4K showcase`, `Inspect every supported HTML and CSS feature tab`, `Switch tabs with keyboard and pointer`, `Capture Simple Vulkan evidence`, `Capture Chrome evidence`, and `Compare all tab captures`. UI captures belong under `doc/06_spec/image/03_system/app/ui.browser/feature/web_renderer_vulkan_4k_showcase_hardening/`.

## Modern SSpec acceptance split

The executable system spec now calls the production inventory,
`HostedWebContentSession`, real layout hit testing, BrowserSession DOM
serialization, and the native tab bridge. Every scenario binds its requirement
locally, uses canonical `step("...")` text, and retains typed HTML/text evidence.
Runner/receipt/Chrome source checks are explicitly folded as **non-acceptance**;
they cannot satisfy the physical Vulkan or parity rows above. The matching
native integration spec owns pointer, keyboard, and atomic-publication details.

Quality gate command (currently unavailable in the deployed CLI):

`bin/simple sspec-maintain scan test/03_system/app/ui.browser/feature/web_renderer_vulkan_4k_showcase_hardening_spec.spl --min-score 90 --no-cache`

Only that tool's reported effective aggregate may be recorded as the score. The
current `bin/release/simple` supports `test`, but reports `file not found:
sspec-maintain`; it therefore cannot establish the required 90+ score.

Current-host physical Vulkan/Chrome execution is mandatory for final PASS when available. Otherwise the checker emits BLOCKED with an exact resume command and retains all host-independent results.

Current receipt diagnostic: the wrapper now selects the normal Apple-Silicon
release artifact and passes the runner as a direct source entrypoint. The
normal artifact nevertheless announces itself as a Rust bootstrap seed while
compiling source; the alternate cached `macos-arm64` artifact exits before
renderer initialization with only `Error running web_render_file_gui.spl`.
Those receipts are FAIL evidence, not a basis for changing the physical
Vulkan/Chrome rows or retrying the renderer without a new eligible runtime.

## Astra review: proof required beyond current scaffolding

The system spec now opens a production `HostedWebContentSession`, injects host
input through real layout targets, and retains live DOM serializations. Its
folded runner/receipt/Chrome checks remain source contracts only; neither those
nor DOM-state checks validate a physical Vulkan frame, measured receipt, or
pixel parity.

| Requirement | Required executable assertion before acceptance |
|---|---|
| REQ-WEB4K-001 | Discover production-supported properties/value families, reconcile the 131/284 inventory discrepancy, reject duplicate/missing IDs, and resolve each row's exact owner and focused test evidence. |
| REQ-WEB4K-002 | Render every supported sample via production APIs; assert its expected geometry/pixel or nonpaint semantic effect. Prove each sample is reachable in its tab and every page/scroll region needed to display it is captured. |
| REQ-WEB4K-003 | Launch the native host, inject pointer and keyboard events, observe selected/focused visuals and retained panel state. Count work across repeated switches and check that hidden panels do not enter layout/paint. |
| REQ-WEB4K-004/005 | Validate independently measured launch-to-present receipt; reject software adapter, headless-only completion, >1,000 ms, missing/stale digests, wrong viewport, missing RSS and incomplete presentation. Test warm-session sample accounting separately. |
| REQ-WEB4K-006/007 | Run both engines on shared composed content/state. Decode every capture, assert tab identity, compare every required sample region with the reviewed tolerance profile, and reject truncated PNG, missing tabs, wrong animation time, or missing backend evidence. |
| REQ-WEB4K-008 | Exercise retained cache invalidation with changing scene pixels, dimensions, backend and device identity; prove collision handling cannot reuse stale content. Verify optimized paint-op order and final pixels on zero/sparse/dense nodes. |

NFR evidence also needs binary/source/fixture identity, monotonic time boundaries, process-tree RSS scope for Chrome, cold/warm cache declarations and repeated-switch retained-memory bounds. The compiler/toolchain blocker prevents runtime execution but does not waive these scenarios or permit source-string checks to cover them. Record each scenario as missing, implemented-unexecuted, failed, blocked or passed independently.
