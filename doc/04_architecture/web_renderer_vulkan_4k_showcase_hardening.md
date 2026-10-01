<!-- codex-design -->
# Web Renderer Vulkan 4K Showcase Hardening Architecture

The required architecture adds declarative inventory and showcase state above the existing renderer. It does not add another display list or backend API. `WebRenderableFeatureInventory` is immutable production-adjacent metadata; the showcase document composer uses `WebShowcaseTab` to select one active document fragment; the normal web pipeline produces canonical Draw IR and Engine2D selects strict Vulkan. These are implementation obligations, not evidence that all integrations already exist.

`WebShowcasePerfReceipt` records Simple execution; `WebRendererComparisonReceipt` joins independently admitted Simple and Chrome rows. Evidence adapters are cold-path tools and cannot run from paint/request hot paths. Physical Vulkan and Chrome backend admission remain separate, fail-closed facts.

Inventory version/digest must key generated showcase content and benchmark captures. A digest mismatch invalidates cached documents and comparisons. Initial startup must render only the default tab; tab switching must reuse parsed inventory/static shell and rebuild only the selected panel. Listing all feature names below the active panel does not satisfy this bound or demonstrate their rendering.

<!-- sdn-diagram:id=web_renderer_vulkan_4k_showcase_hardening.arch -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=web_renderer_vulkan_4k_showcase_hardening.arch hash=sha256:auto render=ascii
@layout dag
@direction LR
Inventory -> ShowcaseModel
ShowcaseModel -> HTMLCSSPipeline
HTMLCSSPipeline -> DrawIR
DrawIR -> Engine2D
Engine2D -> Vulkan
Vulkan -> SimpleReceipt
ChromeModule -> ChromeReceipt
SimpleReceipt -> ComparisonReceipt
ChromeReceipt -> ComparisonReceipt
```
</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=web_renderer_vulkan_4k_showcase_hardening.arch hash=sha256:auto
# run: simple md-diagram-update
```
</details>
<!-- sdn-diagram:end -->

Architecture invariants: no OS branch in app code; no raw Vulkan handle above Engine2D; no lexical occurrence promoted as render evidence; no synthetic timing promoted as Chrome/Simple execution; CPU and unsupported paths remain explicit.

## Astra review — 2026-09-05

The architecture remains suitable, but native interaction, complete visual samples, and admitted receipts are integration gaps. The current runner invokes a static HTML-to-readback call and polls only for close; JavaScript tabs working in Chrome do not establish native Simple interaction. The native host must deliver pointer and keyboard events through the existing input/session owner to the shared tab reducer, then regenerate the selected panel through the production HTML/CSS pipeline. Preserve each tab's content/state across switches and expose focus changes even when selection does not change.

One shared composer must own tab IDs, immutable fixture generation, selected-tab state, and digest creation for both runners. Chrome-specific automation is a separately identified driver; comparison binds the shared content digest and selected state, not an assertion that browser-only activation scripts are identical input. Keep inventory evidence details in the Evidence panel or optional inspection view; each feature's actual demonstration belongs in its assigned panel.

Device-origin readback and positive identities are necessary but insufficient for physical Vulkan admission: Engine2D evidence must also identify adapter/driver and reject software devices. Rendering via Vulkan, GPU readback, host pixel upload, submission completion, and displayed presentation are distinct facts. A host upload via `winit_present_rgba` cannot by itself prove Vulkan presentation or a completed displayed frame. Observe completion through the existing presentation owner and preserve that provenance in the receipt.

The 1-second cold boundary starts before launching the cached executable and ends at confirmed first complete presentation. File reads, inventory construction, backend resolution/initialization, validation and any first-frame upload belong inside it. Render-only and process-to-PNG times are separately labeled diagnostics. Missing presentation or origin timing makes admission incomplete; it cannot be filled with the readback timestamp.
