<!-- codex-design -->
# Web Renderer Vulkan 4K Showcase Hardening — Detail Design

The required `WebRenderableFeatureRow` contract contains stable ID, kind, name, value family, status, production owner, spec path, tab ID, and note. Validation must reject empty IDs/owners for renderable rows and duplicate IDs. Aggregate functions must return stable ordered rows and a deterministic digest. The initial implementation has metadata rows but not this validation/digest contract.

`WebShowcaseState` owns ordered tabs, focused index, and selected index. A session/document owner must retain the inventory digest and cached static shell rather than copying them through every reducer transition. Pure transition functions handle pointer and key actions; the shared composer must emit semantic tab markup plus only the active panel’s feature cards. The initial reducer exists but is not yet connected to native host events.

The runner resolves resolution/backend once, timestamps process-origin milestones, renders via the existing Simple web/Draw IR/Engine2D API, requires strict Vulkan device/readback evidence when requested, presents once, and writes a terminal receipt. Warm redraw and tab measurements reuse the same session.

The Chrome adapter consumes the same generated fixture and tab IDs, records real browser/GPU evidence, and writes an independent receipt. The comparison checker validates digests, dimensions, scale, tab set, backend admission, timings, RSS, and per-tab image diffs before aggregation.

Errors are typed status/reason pairs: invalid inventory, unsupported action, backend mismatch, software Vulkan, incomplete present, stale fixture, missing tab, Chrome unavailable, and pixel threshold failure. None silently fall back.

## Astra review implementation contracts — 2026-09-05

- Inventory discovery must reconcile the production parser/style/layout/paint surface with the existing manifest's 284 CSS rows. The 131-row seed is not a completeness proof. Record the evidence for each inclusion, exclusion or partial value family; generic owner filenames and a broad test filename are insufficient to prove a particular row.
- Each supported row needs a deterministic visual sample and a focused observable assertion. Grouped cards may demonstrate several related properties, but the mapping must identify each property's concrete value, affected geometry/pixels, and evidence. A list item containing a property name does not demonstrate that property. Nonpaint rows require semantic assertions; partial rows identify the exact supported subset.
- `WebShowcasePerfReceipt` must bind schema/version, source and binary digests, composed fixture and inventory digests, tab, viewport and device scale, font/resource identity, backend/adapter/driver, software-device/fallback/degraded flags, timing origin/end kind, cache state, frame digest, sample counts, and max-RSS scope/unit. Unknown fields carry unavailable status rather than fabricated zero measurements.
- An external launcher supplies a monotonic process-origin boundary; the presentation owner supplies matching completion evidence. Emit the first-frame receipt when that milestone occurs, before the close loop. A missing GUI present is an explicitly headless render receipt. A duration over 1,000 ms must fail the performance gate even if rendering succeeded.
- Warm redraw and tab-switch samples reuse one session. Count actual completed frames; record dropped/failed samples. Cold per-tab browser launches cannot populate warm p50/p95. Repeated tab cycles must bound retained panel/cache memory, including the 4K readback and host-presentation buffers.
- `WebRendererComparisonReceipt` must join matching content digests, selected tab, viewport/scale, resource set, scroll position and deterministic animation time. Record each adapter's automation wrapper separately. Freeze animation at the same logical time; elapsed virtual-time budgets alone do not establish that time.
- Pixel comparison needs a reviewed tolerance profile before measurement. Record color/alpha convention, per-channel threshold, permitted differing-pixel ratio, maximum geometry displacement and explicit masks with reasons. No blanket ignore of text, controls, unsupported areas or entire tabs is allowed. Thresholds remain unselected and therefore block final parity admission until reviewed against representative fixtures.
- Chrome process exit after PNG encoding measures cold capture completion, not first presentation. Preserve that metric separately. Decode PNG and verify signature, IHDR, complete image dimensions and selected-panel identity; offsets 16–23 plus a digest do not prove a valid complete capture. Retain bounded stderr and failures for diagnosis.

<!-- sdn-diagram:id=web_renderer_vulkan_4k_showcase_hardening.design -->
<details class="sdn-source"><summary>SDN source</summary>

```sdn id=web_renderer_vulkan_4k_showcase_hardening.design hash=sha256:auto render=ascii
@layout dag
@direction LR
Open -> LoadInventory
LoadInventory -> RenderDefaultTab
RenderDefaultTab -> PresentVulkan
PresentVulkan -> RecordColdReceipt
RecordColdReceipt -> SwitchTab
SwitchTab -> RecordWarmReceipt
RecordWarmReceipt -> CompareChrome
```
</details>
<details class="sdn-ascii" open><summary>Diagram</summary>

```ascii generated-from=web_renderer_vulkan_4k_showcase_hardening.design hash=sha256:auto
# run: simple md-diagram-update
```
</details>
<!-- sdn-diagram:end -->
