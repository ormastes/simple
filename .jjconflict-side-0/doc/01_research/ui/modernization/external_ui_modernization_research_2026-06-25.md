# External Research — "Simple UI Modernization" (Chrome/Safari adaptive CSS)

**Date:** 2026-06-25
**Phase:** 01_research / ui / modernization
**Purpose:** Preserve, verbatim, an externally-authored research note proposing a
Chrome/Safari adaptive CSS architecture and an adaptive-shell layout model for Simple's
GUI / mobile / tablet / TUI / TUI-web renderers. This document is **exploratory input**,
not an adopted design.

> **Provenance & caveats**
> - Authored outside this repository (LLM-assisted external research). It references a
>   downloadable CSS package (`simple-ui-adaptive-css.zip`) that was **not** delivered with
>   the text and is therefore **not** included here. Treat the file listing below as a
>   proposed layering, not shipped artifacts.
> - The note's reading of the codebase is **partly outdated and partly inaccurate.** Several
>   gaps it describes (list/detail, rail→sidebar navigation, two-axis size classes) were
>   **already shipped** via SPipe `mobile-gui-platform` (2026-06-13), and at least one
>   concrete "defect" it cites could **not be reproduced** in the current source.
> - **Do not act on this document directly.** A claim-by-claim verification against the actual
>   source — with file:line evidence and corrections — lives in
>   [`codebase_reconciliation_2026-06-25.md`](./codebase_reconciliation_2026-06-25.md).
>   The adopted, reality-grounded plan lives in
>   [`../../../03_plan/ui/modernization/ui_modernization_plan_2026-06-25.md`](../../../03_plan/ui/modernization/ui_modernization_plan_2026-06-25.md).

---

## Verbatim source

> # Simple UI modernization
>
> [Download the adaptive Chrome/Safari CSS package](sandbox:/mnt/data/simple-ui-adaptive-css.zip)
> *(package not included with the source text; link non-functional here)*
>
> It contains layered source CSS, flattened builds for Simple's partial CSS engine, an accessible example shell, and a phased implementation plan.
>
> ## Main recommendation
>
> Do **not** maintain two complete visual themes for Chrome and Safari. That will drift quickly.
>
> Use:
>
> 1. One shared normalization and component layer.
> 2. Capability detection through `@supports`.
> 3. Small WebKit and Chromium override files.
> 4. Host attributes such as `data-engine="webkit"` and `data-shell="electron"` only for genuine engine or desktop-shell differences.
> 5. A shared semantic shell model that GUI, mobile, tablet, TUI, and TUI-web map to different layouts.
>
> The supplied package follows that architecture:
>
> ```text
> 00-normalize.css
> 10-tokens.css
> 20-base.css
> 30-adaptive-shell.css
> 40-components.css
> 50-effects.css
> 60-motion.css
> 90-webkit.css
> 91-chromium.css
>
> simple-flat-base.css
> simple-flat-webkit.css
> simple-flat-chromium.css
> ```
>
> The normalization layer is based on the approach used by modern-normalize: normalize browser differences while retaining useful native behavior, including consistent box sizing, inherited form typography, WebKit search control handling, and text-size adjustment.
>
> ## Important repository findings
>
> Simple already has the right conceptual foundation: GUI widths use Compact/Regular/Expanded classes at 600 and 840 pixels, GUI height classes use 480 and 900 pixels, and terminal widths use 80 and 160 columns. Its `LayoutProfile` also records both axes and orientation.
>
> The implementation is currently fragmented, however.
>
> ### 1. The classless theme is not an application-shell foundation
>
> `simple_default.css` is suitable for documentation and basic semantic pages, but it centers the body with a constrained maximum width. A desktop/mobile application shell needs a full-window grid and independently scrollable regions instead. Its universal box-sizing rule also omits pseudo-elements.
>
> Keep this theme for generated documents, help, reports, and static pages. Do not evolve it into the IDE/window-manager shell.
>
> ### 2. Current responsive CSS changes size, but not layout morphology
>
> The web renderer has useful compact rules—44-pixel targets, 16-pixel inputs, one-column grids, and a hidden sidebar—but tablet support is mostly a two-column grid. There is no complete bottom-navigation → rail → sidebar transformation, no list/detail state model, no supporting-pane model, and no compact-height treatment.
>
> There is also a concrete CSS defect in the generated glass additions:
>
> ```css
> .widget-menubar {
>   position: sticky;
>   ...
> }
>
> .widget-menubar {
>   position: relative;
>   ...
> }
> ```
>
> The second rule immediately cancels sticky positioning.
>
> ### 3. TUI vertical classification is incorrect
>
> For TUI backends, `terminal_breakpoints()` is used for both width and height. This makes terminal rows use the same 80/160 thresholds as columns, so a normal 80×24 or 120×40 terminal is always vertically Compact.
>
> Add:
>
> ```simple
> fn terminal_height_breakpoints() -> Breakpoints:
>     return Breakpoints(
>         compact_max: 24,
>         regular_max: 40
>     )
> ```
>
> A better TUI model is:
>
> | Class           |  Columns |    Rows | Layout                                    |
> | --------------- | -------: | ------: | ----------------------------------------- |
> | Compact         |    `<80` |   `<24` | One active pane                           |
> | Regular         | `80–119` | `24–39` | Navigation plus workspace, or list/detail |
> | Expanded        |   `≥120` |   `≥40` | Navigation, workspace, supporting pane    |
> | Ultra-wide flag |   `≥160` |       — | Optional diagnostics/inspector pane       |
>
> The ultra-wide condition should be a capability flag rather than a fourth global size class.
>
> ### 4. HTML semantics need correction before further styling
>
> Several interactive widgets are rendered as clickable spans or divs:
>
> * Tabs are `<span>` elements.
> * Checkboxes and radio options are custom `<div>` elements.
> * Workspace tabs, command results, utility-rail items, pills, and context-menu items are also div-based.
>
> CSS alone cannot make those controls robust. Render:
>
> * `<button role="tab">` inside `[role="tablist"]`.
> * Native `<input type="checkbox">` and `<input type="radio">` with labels.
> * Buttons for navigation, pills, menu actions, and command results.
> * `aria-selected`, `aria-controls`, `aria-expanded`, and roving `tabindex`.
> * Arrow-key behavior for tabs and trees.
>
> The WAI patterns define the necessary tab roles, selection state, focus movement, and keyboard behavior.
>
> ### 5. The current TUI-web surface is too minimal
>
> TUI-web currently uses fixed 14-pixel text, a basic centered scroller, and a fixed 24-pixel connection bar. It has no safe-area handling, dynamic viewport sizing, density profiles, responsive terminal scaling, or adaptive status placement.
>
> It should consume the same base tokens and viewport normalization as GUI web, while retaining monospace rendering and terminal cell geometry.
>
> ## Adaptive shell model
>
> All renderers should share these logical regions:
>
> ```text
> AdaptiveShell
> ├── AppBar / TitleBar
> ├── PrimaryNavigation
> ├── MainWorkspace
> ├── SupportingPane or Inspector
> ├── StatusRegion
> └── OverlayHost
> ```
>
> Only the spatial mapping changes.
>
> | Window state               | Navigation                  | Content                                | Inspector/support              |
> | -------------------------- | --------------------------- | -------------------------------------- | ------------------------------ |
> | `<600px`                   | Bottom navigation or drawer | One active pane                        | Bottom sheet/full-screen route |
> | `600–839px`                | Compact rail                | Main pane; optional list/detail switch | Overlay side sheet             |
> | `840–1199px`               | Persistent sidebar          | List and detail side-by-side           | On-demand overlay              |
> | `≥1200px`                  | Persistent sidebar          | Main workspace                         | Persistent supporting pane     |
> | Height `<480px`, landscape | Narrow side rail            | Compact workspace                      | Full-screen overlay            |
>
> This follows current adaptive application practice: compact windows typically use bottom navigation, expanded windows favor a rail, list/detail shows both panes when space permits, and supporting content can become a sheet at narrow widths.
>
> The 1200-pixel condition should **not** replace Simple's 600/840 global breakpoints. Treat it as a local "supporting pane fits" capability.
>
> Use container queries for components inside independently resized windows:
>
> ```css
> .workspace {
>   container: workspace / inline-size;
> }
>
> @container workspace (min-width: 42rem) {
>   .workspace-grid {
>     grid-template-columns: repeat(2, minmax(0, 1fr));
>   }
> }
>
> @container workspace (min-width: 62rem) {
>   .list-detail {
>     grid-template-columns:
>       minmax(15rem, 0.36fr)
>       minmax(0, 0.64fr);
>   }
> }
> ```
>
> Container queries are now broadly available, but Simple's own CSS parser does not yet claim full modern CSS support. Therefore, retain media-query/grid fallbacks and use the flattened package builds for staged internal-renderer adoption.
>
> ## Chrome/Safari normalization strategy
>
> Use this metadata in both `src/app/ui.web/html.spl` and `src/app/ui.tui_web/html.spl`:
>
> ```html
> <meta
>   name="viewport"
>   content="width=device-width, initial-scale=1, viewport-fit=cover"
> >
> <meta name="color-scheme" content="dark light">
> ```
>
> The current generated pages only set width and initial scale.
>
> `viewport-fit=cover` plus `env(safe-area-inset-*)` is necessary for edge-to-edge WebKit layouts. Dynamic viewport units should replace fixed `100vh` where possible because mobile browser UI changes the visible viewport. `color-scheme` lets browsers render form controls, scrollbars, and the document canvas consistently with the selected theme.
>
> Set engine identity in generated markup:
>
> ```html
> <html data-engine="webkit" data-shell="tauri" data-platform="macos">
> <html data-engine="webkit" data-shell="webview" data-platform="ios">
> <html data-engine="chromium" data-shell="electron">
> <html data-engine="chromium" data-shell="web">
> ```
>
> Do not infer this with CSS user-agent hacks. The backend already knows which shell it launched.
>
> ### WebKit-only CSS
>
> The WebKit file should be limited to:
>
> * `-webkit-backdrop-filter`.
> * WebKit search decoration removal.
> * `-webkit-user-select` for native titlebar drag regions.
> * Transparent tap highlight where a replacement pressed state exists.
> * A minimum 16-pixel form-control font on coarse-pointer devices.
> * Confirmed Safari/WKWebView defects found by tests.
>
> ### Chromium-only CSS
>
> The Chromium file should primarily contain Electron-native behavior:
>
> ```css
> html[data-engine="chromium"][data-shell="electron"]
> .app-titlebar__drag {
>   -webkit-app-region: drag;
> }
>
> html[data-engine="chromium"][data-shell="electron"]
> :is(button, input, select, textarea, a, [role="button"]) {
>   -webkit-app-region: no-drag;
> }
> ```
>
> Visual styling should not diverge merely because the engine is Chromium.
>
> Avoid applying `appearance: none` globally to every form control. It can remove the visible native widget, so use it only on classes whose hover, focus, checked, disabled, error, and high-contrast states are all implemented.
>
> ## Better HTML platform techniques
>
> Use native `<dialog>` for modal dialogs and sheets. It provides top-layer placement, modal focus handling, a backdrop, and makes the rest of the document inert when opened with `showModal()`.
>
> Use the Popover API for nonmodal command menus, context menus, suggestion lists, and lightweight inspectors. Keep a deterministic fallback for Simple's internal browser. Popovers are nonmodal and are suited to action menus, suggestions, and content pickers; modal decisions should remain dialogs.
>
> Other changes:
>
> * Put a button inside sortable table headers and maintain `aria-sort`.
> * Associate filters and form fields with visible `<label>` elements.
> * Give toasts `role="status" aria-live="polite"`; use `role="alert"` only for urgent failures.
> * Distinguish keyboard focus from selected state in trees and lists.
> * Escape all text and attribute content before string interpolation. Current renderers directly interpolate properties into HTML, so this is also an injection-hardening requirement.
> * Replace inline width/height declarations with CSS variables or data attributes so responsive CSS can override them.
> * Apply `content-visibility: auto` only to long offscreen lists and report sections, never active dialogs, focus targets, or currently selected panels.
>
> ## Effects and visual direction
>
> Simple already has a sophisticated modern-window concept—rounded translucent surfaces, motion modes, focus rings, widgets, command palettes, and browser audits. The issue is not a shortage of effects; it is insufficient restraint and consolidation.
>
> The existing prototype uses blur around 40 pixels, a liquid animated background, fixed 800×540 windows, and fixed 240-pixel sidebars. It is useful as art direction but should not become production geometry.
>
> Use this material budget:
>
> | Surface                         |    Blur | Shadow  | Use                                |
> | ------------------------------- | ------: | ------- | ---------------------------------- |
> | Navigation                      |  8–10px | Minimal | Titlebar, rail, dock               |
> | Panel                           | 12–14px | Medium  | Inspector, cards, command surfaces |
> | Modal                           | 16–18px | Strong  | Dialog or important overlay        |
> | Low-energy/reduced transparency |     0px | Minimal | Solid fallback                     |
>
> Rules:
>
> * Never stack several blurred ancestors.
> * Keep an opaque baseline before the `@supports` enhancement.
> * Avoid blur on large scrolling content.
> * Use one focal background gradient, not several equally strong animated layers.
> * Remove `transition: all`; list the properties being animated.
> * Use accent glow only for selection, focus, or active work—not every panel.
>
> `backdrop-filter` requires transparency to reveal the backdrop and should be treated as progressive enhancement.
>
> ## Motion system
>
> Retain Simple's existing `data-wm-motion`, transparency, energy, and quiet-mode controls, but centralize them into tokens:
>
> ```css
> --ui-duration-instant: 80ms;
> --ui-duration-fast:    120ms;
> --ui-duration-base:    180ms;
> --ui-duration-slow:    240ms;
>
> --ui-ease-standard:   cubic-bezier(0.2, 0, 0, 1);
> --ui-ease-emphasized: cubic-bezier(0.2, 0.8, 0.2, 1);
> ```
>
> Recommended timing:
>
> * Hover and press: 80–120ms.
> * Selection and focus: 120–180ms.
> * Panel entrance: 180–240ms.
> * Sheet or modal: no more than about 280ms.
> * Closing: approximately 70–80% of the opening duration.
> * Repeated animation: only progress indicators or explicitly enabled ambient wallpaper.
>
> Frequently triggered transitions should affect `transform`, `opacity`, colors, borders, or shadows—not dimensions and layout position.
>
> In reduced-motion mode, remove panning, scaling, dock magnification, wallpaper drift, and looping animation. Preserve immediate opacity or color feedback so actions remain perceptible. The media query exists specifically to substitute or remove nonessential motion for users who request it.
>
> View Transitions can enhance workspace or route changes, but they should be feature-detected at runtime and never be required for navigation:
>
> ```javascript
> function updateWorkspace(update) {
>   if (!document.startViewTransition) {
>     update();
>     return;
>   }
>
>   document.startViewTransition(update);
> }
> ```
>
> Browser support is improving, but capability detection remains the correct contract across Chrome, Safari, embedded WebViews, and Simple's renderer.
>
> ## Implementation order
>
> **P0 — Browser parity:** add normalization, head metadata, safe areas, dynamic viewport units, sticky-rule fix, coarse-pointer sizing, and boundary screenshots.
>
> **P1 — Adaptive shell:** introduce shared shell slots, navigation morphology, list/detail, supporting-pane behavior, and compact-height handling.
>
> **P2 — Semantic widgets:** replace interactive divs/spans, add keyboard models, native dialog/popover paths, labels, live regions, and escaping.
>
> **P3 — Effects and motion:** consolidate glass generators, enforce material and blur budgets, remove `transition: all`, and centralize reduced/off modes.
>
> **P4 — TUI parity:** add terminal height breakpoints and map the same semantic shell into one-, two-, and three-pane terminal layouts.
>
> **P5 — Quality gates:** extend the repository's existing structural-layout, screenshot, geometry, and pixel-comparison infrastructure rather than creating a separate audit system. The repository already has most of that foundation.
>
> Test the 599/600 and 839/840 boundaries explicitly, plus 390×844, 430×932, 768×1024, 1024×768, 1280×800, and 1440×900. Include real Safari/WKWebView smoke tests, Chromium/Electron, 200% zoom, enlarged text, keyboard-only use, touch input, dark/light mode, reduced motion, forced colors, and transparency-off mode. Coarse-pointer targets should remain at least 44 pixels; focus must never be hidden behind titlebars, bottom navigation, or sheets. WCAG's formal target-size and focus-obscuration requirements are lower-level minimums, so Simple's existing 44-pixel policy is a sound stronger default.
>
> The two Instagram media pages could not be retrieved reliably through Instagram's public surface in this environment, so I have not invented colors, geometry, or motion details for them. Attach screenshots of those posts for a precise visual-token mapping.

---

## Cited external sources (from the note)

1. modern-normalize — https://github.com/sindresorhus/modern-normalize
2. WAI-ARIA APG, Tabs pattern — https://www.w3.org/WAI/ARIA/apg/patterns/tabs/
3. Android — Build adaptive navigation — https://developer.android.com/develop/ui/compose/layouts/adaptive/build-adaptive-navigation
4. MDN — `@container` — https://developer.mozilla.org/en-US/docs/Web/CSS/@container
5. WebKit — Designing for iPhone X (safe areas) — https://webkit.org/blog/7929/designing-websites-for-iphone-x/
6. MDN — `appearance` — https://developer.mozilla.org/en-US/docs/Web/CSS/appearance
7. MDN — `<dialog>` — https://developer.mozilla.org/en-US/docs/Web/HTML/Reference/Elements/dialog
8. MDN — Popover API — https://developer.mozilla.org/en-US/docs/Web/API/Popover_API
9. MDN — `content-visibility` — https://developer.mozilla.org/en-US/docs/Web/CSS/content-visibility
10. MDN — `backdrop-filter` — https://developer.mozilla.org/en-US/docs/Web/CSS/backdrop-filter
11. MDN — `prefers-reduced-motion` — https://developer.mozilla.org/en-US/docs/Web/CSS/@media/prefers-reduced-motion
12. Chrome — View Transitions — https://developer.chrome.com/docs/web-platform/view-transitions/
13. W3C WCAG 2.2 — Target Size (Minimum) — https://www.w3.org/WAI/WCAG22/Understanding/target-size-minimum.html
