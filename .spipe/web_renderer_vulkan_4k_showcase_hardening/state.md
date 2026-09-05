# Feature: Web Renderer Vulkan 4K Showcase Hardening

## Raw Request
$spipe harden simple web renderer backed with vulkan. 1. imporve perf drawing 4k web rendering showcase in a sec or less. compare with chrome module. 2. check all rendering features renderable tags, and css list them and update show cases. tab to switchable. update web renderer show case to show all element of html and css renderable. and let showcase open in a sec. do not break feature or arch.

## Task Type
feature

## Refined Goal
Harden the canonical Simple web renderer and showcase so a Vulkan-backed 4K all-supported-HTML/CSS catalog opens and renders within one second, exposes switchable tabs, and produces fail-closed performance and visual comparison evidence against Chrome without bypassing established Draw IR, Engine2D, or backend architecture.

## Acceptance Criteria
- AC-1: A canonical machine-readable inventory enumerates every HTML tag and CSS property/value family the production Simple renderer classifies as renderable, partially renderable, or unsupported, and every renderable row traces to production code plus focused executable evidence.
- AC-2: The production web showcase is generated from or checked against that inventory, visibly exercises every renderable HTML and CSS row without exact-fixture shortcuts, and reports any unsupported or partial row honestly instead of silently omitting it.
- AC-3: The showcase provides keyboard and pointer-accessible switchable tabs with stable selection/focus semantics, bounded content/layout work per switch, and regression coverage for initial selection, switching, focus, and retained content.
- AC-4: The installed/canonical showcase entrypoint opens a 3840x2160 showcase and reaches its first complete presented frame in at most 1,000 ms on an admitted Vulkan-capable host; timing includes process startup, parse/style/layout/paint, backend initialization, submission, and presentation and records exact binary, fixture, adapter/driver, backend, viewport, frame hash, and max RSS.
- AC-5: Warm 4K redraw and tab-switch measurements use representative catalog content, publish p50/p95 and dropped/fallback/readback fields, and demonstrate that requested Vulkan work executes on a real Vulkan device with no software, CPU, mock, or browser fallback counted as PASS.
- AC-6: An equivalent Chrome module renders the same versioned 4K catalog and records comparable startup/first-complete-frame, warm redraw/tab-switch, viewport, frame, GPU-backend, and max-RSS evidence; the comparison report explains unavoidable semantic or instrumentation differences and never promotes Chrome availability alone as Vulkan proof.
- AC-7: Pairwise image/readback comparison between Simple Vulkan and Chrome covers every showcase tab at matching viewport/device scale, uses documented tolerances, emits machine-readable mismatch evidence, and fails closed on missing captures, backend proof, incomplete tab coverage, or threshold violation.
- AC-8: Performance work removes measured hot-path waste while preserving canonical BrowserSession -> HTML/CSS -> Draw IR -> Engine2D -> Vulkan ownership, startup/cache invalidation correctness, deterministic pixels, CPU/backend fallback semantics, and established public interfaces; no per-OS app fork or renderer-specific architecture bypass is introduced.
- AC-9: Focused unit/integration/SSpec scenarios cover the inventory, complete showcase surface, tab interaction, 4K timing receipt validation, strict Vulkan admission, Chrome comparison, pixel/readback parity, unsupported-feature reporting, and failure paths; generated/manual SPipe documentation reads as an operator manual and contains no placeholder assertions.
- AC-10: Existing renderer, GUI, Draw IR, Engine2D, backend-selection, and HTML/CSS conformance tests affected by this lane remain green once; direct runtime/env guards pass for working and staged scope, and `doc/06_spec` contains zero executable `*_spec.spl` files.
- AC-11: Knowledge is refreshed in the matching research, selected feature/NFR requirements, architecture, detail design, system-test plan, agent plan, `doc/07_guide` operator/developer guide, feature-expert and layer-expert `skill.md` files; every discovered but unfixed gap has a `doc/08_tracking/bug` record with file:line, owner, and actionable unblock condition. Workflow/skill/command docs are N/A unless this lane changes their behavior.
- AC-12: Verification publishes requirement-to-evidence traceability and a final PASS only when all current-host performance, Vulkan, Chrome, catalog, tab, parity, architecture, and documentation gates are proven; unavailable external capability remains an explicit blocker with retained artifacts and an exact resume command, never a skip or inferred pass.

## Scope Exclusions
- Implementing currently unsupported HTML/CSS semantics is outside this lane unless a missing semantic is required to make an already-declared renderable row truthful.
- Cross-platform Vulkan performance claims require execution on each claimed platform; this lane does not infer them from the current host.
- Release/version bump/push is not requested.

## Cooperative Review
This is a broad renderer, benchmark, showcase, and evidence lane. Lower-model sidecars may independently audit (1) HTML/CSS inventory-to-production traceability, (2) showcase/tab behavior and SSpec/manual coverage, and (3) performance/Chrome/Vulkan evidence contracts. Merge owner: root Codex. Final reviewer: normal/highest-capability Codex. Shared interfaces: `WebRenderableFeatureInventory`, `WebShowcaseTab`, `WebShowcasePerfReceipt`, and `WebRendererComparisonReceipt`. Manual step flow: `Open the Vulkan 4K showcase`, `Inspect every supported HTML and CSS feature tab`, `Switch tabs with keyboard and pointer`, `Capture Simple Vulkan evidence`, `Capture Chrome evidence`, and `Compare all tab captures`. Setup/checker helpers: `setup_web_showcase_4k_fixture`, `check_web_showcase_inventory`, `check_web_showcase_vulkan_receipt`, and `check_web_showcase_chrome_comparison`. Any scaffold placeholder must use `assert(false)` or `fail(...)` until real behavior exists. Generated-manual review owner: root Codex.

## Runtime Boundary Decision
- runtime_need: Existing web-render, Engine2D, Vulkan presentation, input, timing, process, and file capabilities; new raw runtime hooks are not presumed.
- facade_checked: Canonical BrowserSession/web-renderer, Draw IR, Engine2D backend/session, UI input, clock/process, and evidence-file facades must be reused before any lower-level change.
- chosen_path: Extend production facades and retained data structures only where profiling or traceability evidence requires it.
- rejected_shortcuts: No exact-showcase drawing, fake Vulkan identity, unbounded shell-out in a hot path, raw local `rt_env_get`/`rt_process_run`, Chrome screenshot standing in for Simple evidence, or Rust-seed fallback.

## Research Summary

### Existing Code
- `examples/06_io/ui/web_standards_showcase_gui.spl:14-27,91-94` — canonical example entry, currently imports missing runner/resolution APIs.
- `examples/06_io/ui/web_render_file_gui.spl:35-38,61-121` — current runner is 80×60 CPU-SIMD and references undefined receipt/backend values.
- `src/lib/common/ui/showcase_catalog.spl:33-68` — canonical catalog identity and deliberately false installed readiness.
- `scripts/check/check-html-css-rendering-manifest-traceability.shs:38-47,99-165` — lexical tag/property fixture coverage, not production render proof.
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_style.spl:336-343` — production nonpaint/default tag behavior.
- `test/05_perf/web_render_chrome/simple_runner.spl:196-233` and `chrome_runner.spl:115-143` — synthetic comparison placeholders.

### Reusable Modules
- Production Simple web layout/paint modules, Draw IR/Engine2D backend/readback, showcase catalog, retained web host, and Chrome component-renderer orchestration are reusable; widget-only perf gates are not equivalent.

### Domain Notes
- First-complete-frame includes startup through presentation; Vulkan needs physical device proof; HTML nonpaint semantics and CSS value families require explicit status; accessible tabs need semantic roles and keyboard/pointer parity.

### Open Questions
- NONE; unavailable live physical Vulkan or Chrome evidence remains a verification blocker rather than a design ambiguity.

<!-- sdn-diagram:id=web_renderer_vulkan_4k_showcase_hardening.research -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_renderer_vulkan_4k_showcase_hardening.research hash=sha256:auto render=ascii
@layout dag
@direction LR

Inventory -> Showcase
Showcase -> SimpleWebRenderer
SimpleWebRenderer -> DrawIR
DrawIR -> Engine2D
Engine2D -> VulkanEvidence
Showcase -> ChromeHarness
VulkanEvidence -> ComparisonReceipt
ChromeHarness -> ComparisonReceipt
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_renderer_vulkan_4k_showcase_hardening.research hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

## Requirements
- REQ-1 (AC-1/2): production-backed typed HTML/CSS inventory drives a complete, honest showcase — area: browser engine + showcase fixture.
- REQ-2 (AC-3): accessible pointer/keyboard tab state and bounded switching — area: showcase UI/input.
- REQ-3 (AC-4/5): source-bound 4K cold/warm receipts with strict physical Vulkan admission and ≤1,000 ms first complete frame — area: runner + perf evidence.
- REQ-4 (AC-6/7): equivalent real Chrome 4K measurement and all-tab pixel/readback comparison — area: Chrome harness + comparison checker.
- REQ-5 (AC-8): preserve BrowserSession -> Draw IR -> Engine2D -> Vulkan ownership, cache correctness, deterministic pixels, and fallbacks — area: architecture + renderer.
- REQ-6 (AC-9/10): focused executable coverage, manuals, regression gates, runtime guards, and spec layout hygiene — area: test + scripts/check + doc/06_spec.
- REQ-7 (AC-11/12): refresh knowledge and retain fail-closed blockers/evidence traceability — area: doc/ + tracking.

## Specs

- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_showcase_tabs_spec.spl` — pure focus/selection, keyboard, pointer, and semantic-markup coverage for AC-3.
- `test/03_system/app/ui.browser/feature/web_renderer_vulkan_4k_showcase_hardening_spec.spl` — portable catalog and strict runner contract for AC-3/4/5; Chrome remains deliberately blocked.
- `doc/06_spec/03_system/app/ui.browser/feature/web_renderer_vulkan_4k_showcase_hardening_spec.md` — authored operator manual pending Stage-4 docgen regeneration.

## Implementation Status

- Repaired the canonical showcase runner APIs and removed undefined receipt variables and the 80×60 CPU-only path.
- Added a 4K default, strict Vulkan device-readback admission, degraded-render rejection, and first-complete-frame timing fields.
- Added a pure seven-tab state model plus accessible tab markup and updated the bundled showcase with real tablist/tabpanel semantics and keyboard/pointer JavaScript.
- Added `WebRenderableFeatureInventory` v1 with 113 HTML and all 284 CSS names claimed by the canonical traceability source, conservative renderable/partial/nonpaint/unsupported status, production/test owner and tab mappings; the runner injects every row into the rendered showcase and reports both counts.
- Replaced growth-strategy-dependent looped bare `Array.push` paint-op construction with a bounded preallocated buffer and one linear ordered-prefix finish; a runtime measurement is still required before calling the old path quadratic.
- Replaced full serialized Draw IR text in the 16-entry GPU route-cache key with a SHA-256 identity plus byte length while retaining current-frame pixel/device validation.
- `bin/simple` remains bootstrap-only, but the deployed `bin/release/simple` exposes `test` and reaches the renderer test path. Its test runner presently completes session setup and then emits no scenario result for renderer specs; bounded diagnostic processes were stopped after observation. The unavailable `sspec-maintain` subcommand still prevents an authoritative Modern SSpec score. Rust seed and untracked Phase-2 substitution remain forbidden.
- The observed ~1.69 GiB compile is attributed to the existing retain-all parser/AST path, not the rewritten runner: its source shrank and retained the same two heavy module imports. Future probes must use explicit source roots, entry closure, low-memory, one thread, isolated cache, and resource guards.
- Replaced the synthetic-only Chrome runner with bounded real 3840×2160 headless PNG capture, exact IHDR/digest admission, and seven canonical tab captures. It deliberately records GPU backend and warm aggregates as unverified and `comparison_admitted=false` until those real evidence rows exist.
- Corrected fixture equivalence: the Chrome harness now injects the same generated typed inventory markup as the Simple runner before selecting each tab, rather than comparing a smaller static page against Simple's runtime-expanded page.
- Captured and visually inspected a real 3840×2160 Chrome Overview PNG (131,185 bytes, SHA-256 `2244e432849e49a6c631939a7a7fcfe0ff59cae381788d8893bdbd8c31a94337`) in 5.87 seconds cold. It is documented as non-admitted because it predates the shared-fixture correction and lacks GPU, warm-frame, and RSS proof.
- Added a retained native tab path: Winit ordered input routes through `HostedWebContentSession`, resolves real DOM semantic targets, and applies one bounded atomic BrowserSession update for `aria-selected`, roving `tabindex`, and panel `hidden` state. It preserves the document generation and unrelated form/page state; generic fixture JavaScript support remains a separately tracked gap.
- Added production-generated, per-row showcase witnesses: safely embeddable renderable HTML rows use valid element samples with required parent structures, renderable CSS rows use selected inert declaration samples, and structural/partial/nonpaint/unsupported rows stay explicit classification cards. Witnesses never claim pixel verification.
- Added `scripts/check/check-web-showcase-4k-receipt.shs`, an external fail-closed receipt wrapper binding the deployed binary, fixture and runner digests plus 4K/Vulkan wall-time and RSS fields. Its current retained receipt at `build/web_renderer_vulkan_4k_showcase_hardening/simple/receipt.lgJ6hh/receipt.env` is `BLOCKED unsupported-bootstrap-cli`; no renderer run or fallback occurred.
- Host-independent safety gates passed once after the current renderer/runner/native-input changes: `direct-env-runtime-guard.shs --working`, `--staged`, and the `doc/06_spec` executable-spec layout guard (zero misplaced specs).

## Phase
implementation-active

## Log
- dev: Created state file with 12 acceptance criteria (type: feature); prior goal turn classified as no progress because it had not yet changed authoritative state or gathered current evidence.
- research: Audited canonical inventory, showcase, production renderer, Vulkan/Chrome evidence, and existing tests; found 7 reusable areas and mapped 7 requirements. Three independent sidecars returned FAIL on current completion evidence.
- design: Added selected feature/NFR requirements, GUI/architecture/detail design, test plan, and cooperative agent plan.
- spec: Added focused tab and portable showcase contract specs plus an authored manual; docgen is held for an admitted Stage-4 CLI.
- implement: Repaired the runner and added tab state/markup/page interaction. Focused execution attempt was blocked by the deployed bootstrap-only CLI.
- optimize: Parallel perf/memory lanes hardened tile-op allocation and removed serialized-scene cache retention; focused tests were added but could not be executed with the bootstrap-only CLI.
- knowledge: Updated the showcase guide plus web-render feature and UI-render layer expert notes without advertising the still-unreachable installed capability.
- implement: Connected the typed inventory to the production showcase render input and added a fail-closed real Chrome 4K capture foundation; neither is promoted as final parity/performance PASS.
- evidence: Recorded the first real Chrome 4K Overview capture and corrected the harness so future Simple/Chrome tab captures consume identical inventory-expanded source. The current capture remains a diagnostic baseline, not comparison PASS evidence.
- implement: Added native BrowserSession-owned tab selection/focus updates and integration coverage for pointer, Arrow/Home/End/Enter/Space, generation preservation, and invalid atomic batches. The suite cannot yet execute on the admitted CLI.
- inventory: Reconciled the typed CSS inventory from 131 to all 284 names in the canonical claimed-property set; newly covered names are classified partial, nonpaint, or unsupported unless a production rendering owner is established.
- evidence: Added and executed the external 4K receipt wrapper. It retained a bootstrap-only CLI blocker before renderer execution and leaves scanout, physical-device, warm/RSS, and Chrome parity acceptance active.
- implement: Added compact, safe real-element and CSS declaration witnesses to the shared Simple/Chrome fixture composer; catalog contracts check witness coverage, context-sensitive markup, inactive-tab placement, and honest non-renderable classification.
- verify: Current working/staged runtime facade guards and generated-spec layout guard PASS. Execution, backend, timing, and parity gates remain active because the deployed CLI is bootstrap-only.
- verify: Modern SSpec source was exercised with the deployed release test runner. It first exposed invalid `case` match-arm and unparenthesized multiline-boolean forms in the new specs, then a transitive parse failure in `browser_renderer_protocol`; all were corrected. A focused existing browser-renderer smoke test and the repaired system spec now both complete runner setup but remain live without producing scenarios, so their exact processes were stopped rather than allowed to run indefinitely. This is a test-runner execution blocker, not a performance/pass result.
- evidence: Corrected the external receipt wrapper to select the normal Apple-Silicon release artifact rather than the `-macho` bootstrap sibling and to invoke source entrypoints using the deployed CLI's documented `<file.spl>` form. The normal artifact still announced itself as a Rust bootstrap seed when it compiled source and failed in legacy `utf8.spl` parsing; the distinct `macos-arm64` cached runtime is non-bootstrap by version but exits `1` in 0.04 seconds with only `Error running web_render_file_gui.spl`. Both receipts are retained as fail-closed diagnostics (`receipt.4AJjpz` and `receipt.9cAiPA`); neither entered rendering, so no performance, Vulkan, or parity status changed.
