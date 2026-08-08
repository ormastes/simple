# UI Modernization Plan — Desktop & Mobile App Layout

**Date:** 2026-06-25
**Phase:** 03_plan / ui / modernization
**Purpose:** A reality-grounded plan to modernize Simple's UI across desktop (Electron/Tauri,
window-manager shell) and mobile (Tauri2/WKWebView/Android WebView), derived from the external
modernization note **after** verifying it against the source.
**Inputs:**
- Research (external, verbatim): [`../../../01_research/ui/modernization/external_ui_modernization_research_2026-06-25.md`](../../../01_research/ui/modernization/external_ui_modernization_research_2026-06-25.md)
- Deep research (reconciliation, file:line evidence): [`../../../01_research/ui/modernization/codebase_reconciliation_2026-06-25.md`](../../../01_research/ui/modernization/codebase_reconciliation_2026-06-25.md)

**Scope guardrails (do not redo shipped work):** the theme system, two-axis size classes
(600/840 + 480/900), native `adaptive_nav_scaffold()` / `list_detail_scaffold()`, web/Tauri/Chrome
pixel parity, the server-authoritative WM/WSS protocol, the UI Access Protocol, and the HTML/CSS
toolchain are **already shipped/production**. This plan **wires the HTML renderers into** that
foundation and closes confirmed gaps — it does **not** introduce a parallel system.

**Hard constraints (from reconciliation §5):**
- The in-house CSS parser implements `@media`, `var()`, flexbox, sticky, transforms/animations, and
  **partial `@supports`** — but **no CSS Grid and no `@container`**. Every layout this plan adds must
  work with **flexbox + `@media` + the scaffold API**. Container queries / View Transitions are
  **optional progressive enhancement, never required**, runtime feature-detected for Chrome/Safari only.
- Reuse existing quality gates (structural-layout SDN, screenshot, geometry, pixel-parity) rather than
  building new audit tooling.

---

## 1. Design spine: one shell model, mapped per surface

Adopt the note's logical-region model, but realize it through the **shipped scaffold API**, not new CSS:

```
AdaptiveShell
├── AppBar / TitleBar        (drag region on desktop; status-safe top on mobile)
├── PrimaryNavigation        (bottom bar | rail | sidebar — by width class)
├── MainWorkspace            (single pane | list+detail — by width class)
├── SupportingPane/Inspector (overlay sheet | persistent pane — by "fits" capability)
├── StatusRegion
└── OverlayHost              (dialogs, popovers, toasts)
```

Spatial mapping keys off the **existing** `LayoutProfile` (width × height class + orientation), plus a
**local** "supporting-pane fits" capability (≈1200px) that the note correctly says must **not** become a
4th global breakpoint. The native engine already does this; the work is to make the **generated HTML/CSS**
do the same.

| Width class (existing) | Navigation | Workspace | Supporting pane |
| --- | --- | --- | --- |
| Compact `<600` | Bottom bar / drawer | One active pane | Bottom sheet / full route |
| Regular `600–839` | Compact rail | Main; optional list/detail | Overlay side sheet |
| Expanded `840–1199` | Persistent sidebar | List + detail side-by-side | On-demand overlay |
| Expanded `≥1200` (fits-flag) | Persistent sidebar | Main workspace | Persistent inspector |
| Height `<480` landscape | Narrow side rail | Compact workspace | Full-screen overlay |

---

## 2. Desktop app layout (Electron / Tauri / WM shell)

**Goal:** a full-window application shell with independently scrollable regions and a native-feeling
title bar — *not* the centered, max-width document theme (`simple_default.css` stays for docs/help/reports).

1. **App-shell grid (not the doc theme).** Add a `.app-shell` full-viewport grid
   (`grid` is unavailable in the in-house parser → use **flexbox rows/columns + `100dvh`**) with fixed
   AppBar/StatusRegion and flex-growing Nav/Workspace/Support that scroll independently. Keep
   `simple_default.css` reserved for generated documents; do not evolve it into the shell.
2. **Persistent sidebar at Expanded, rail at Regular.** Drive Nav morphology from the width class via the
   shipped `adaptive_nav_scaffold()`; emit the corresponding HTML/CSS instead of a static sidebar.
3. **List/detail at ≥840.** Use `list_detail_scaffold()` to emit two panes side-by-side; single pane +
   push navigation below 840.
4. **Supporting/inspector pane.** Persistent at ≥1200 ("fits" flag); overlay side-sheet at 600–1199;
   bottom sheet/full route under 600. Realize overlays with native `<dialog>` (modal) / Popover (nonmodal)
   — see §6.
5. **Native title bar & window controls (Electron/Chromium).** Emit a drag region:
   ```css
   html[data-engine="chromium"][data-shell="electron"] .app-titlebar__drag { -webkit-app-region: drag; }
   html[data-engine="chromium"][data-shell="electron"]
     :is(button,input,select,textarea,a,[role="button"]) { -webkit-app-region: no-drag; }
   ```
   Visual styling must **not** diverge merely because the engine is Chromium; only behavior does.
6. **Compact-height (laptop / split / landscape).** When height class is Compact, switch the sidebar to a
   narrow rail and compress vertical padding; ensure focus targets never hide behind the title bar.
7. **Density.** Desktop uses the dense touch-target floor (~32px) from `form_factor.spl`; do not force the
   44px mobile floor on fine-pointer desktops, but keep ≥44px on coarse-pointer (`@media (pointer: coarse)`).

**Desktop acceptance:** boundary screenshots at 1280×800 and 1440×900 plus the 839/840 and 1199/1200
transitions; sidebar↔rail↔bottom morphology verified through the existing pixel-parity gate on
Electron and Tauri/WebKitGTK; window drag region works; doc theme unchanged for generated documents.

---

## 3. Mobile app layout (Tauri2 webview / iOS WKWebView / Android WebView)

**Goal:** edge-to-edge, safe-area-correct, touch-first layouts that reuse the same shell model and tokens
as desktop, with WebKit/WKWebView quirks handled as small overrides.

1. **Viewport + safe areas.** Emit
   `<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">` and
   `<meta name="color-scheme" content="dark light">`; pad the shell with `env(safe-area-inset-*)`.
   *(Today both renderers emit only width+initial-scale — reconciliation §4.)*
2. **Dynamic viewport units.** Replace fixed `100vh` with `100dvh` for full-height regions so mobile
   browser chrome resizing doesn't clip the workspace; keep a `vh` fallback.
3. **Bottom navigation under 600; drawer for overflow.** From `adaptive_nav_scaffold()`. Landscape phones
   (height Compact) switch to a narrow side rail rather than stealing vertical space with a bottom bar.
4. **List/detail with push navigation.** Under 840: list → detail is a push route, back returns to list;
   at ≥840 (large tablets / landscape): side-by-side via `list_detail_scaffold()`.
5. **Supporting content as sheets.** Inspector/secondary content becomes a bottom sheet (Compact) or side
   sheet (Regular) using native `<dialog>`/Popover; never a permanently docked pane on phones.
6. **Touch ergonomics.** 44px minimum targets on coarse pointers (already policy in `form_factor.spl`);
   16px minimum form-control font on coarse pointers to prevent iOS zoom-on-focus (WebKit override file).
7. **Tablet morphology (the real gap).** Current generated CSS only collapses to one column at 768px
   (reconciliation §3). Add genuine tablet behavior via the scaffolds (rail + list/detail at 600–839,
   sidebar + side-by-side at ≥840) — **not** a hand-tuned two-column grid.

**Mobile acceptance:** boundary screenshots at 390×844, 430×932, 768×1024, 1024×768; real WKWebView and
Android WebView smoke tests; safe-area insets visible on notched devices; no iOS focus-zoom; bottom
nav↔rail↔sidebar and list↔detail transitions verified.

---

## 4. Accessibility & semantics (web renderers) — confirmed gap

Target file: `src/app/ui.render/html_widgets.spl` (verified emitter; reconciliation §4).

- Tabs → `<button role="tab">` inside `[role="tablist"]` with `aria-selected`/`aria-controls`, roving
  `tabindex`, arrow-key movement (current: `<span>` @ `:363`).
- Checkbox/radio → native `<input type=checkbox|radio>` + `<label>` (current: `<div>` @ `:393,:410,:419`).
- Pills, utility-rail items, context-menu items, workspace tabs, command results → `<button>` with proper
  roles (current: `<div data-action>` @ `:660,:704,:728,:750`).
- Trees: expose `aria-expanded`; distinguish keyboard focus from selection state.
- Sortable headers: button inside `<th>` + `aria-sort`. Toasts: `role="status" aria-live="polite"`
  (`role="alert"` only for urgent failures).

**Acceptance:** keyboard-only traversal of tabs/trees/menus; the UI Access Protocol's `visual_probe`
reports the new roles/states; AT smoke on at least one screen reader path.

---

## 5. Security — output escaping (confirmed, do early)

`html_escape()` exists (`src/app/ui.render/html.spl:11-19`) but is **not applied** in `html_widgets.spl`
(reconciliation §4): labels, titles, `value`, `placeholder`, `src`, `alt`, and `data-action` are
interpolated raw at `:384,:393,:410,:419,:446,:451,:461`. **Apply `html_escape()` to every interpolated
property/text** and add a regression test that a `<script>`/`"`/`&` payload in a widget label is escaped.
Treat as a security fix, not just hygiene.

---

## 6. Platform HTML techniques

- **Native `<dialog>`** (`showModal()`) for modal dialogs/sheets — top-layer, focus-trap, inert backdrop.
- **Popover API** for nonmodal command menus, context menus, suggestions, lightweight inspectors —
  with a **deterministic fallback** path for Simple's in-house browser (feature-detect at runtime).
- `content-visibility: auto` only on long offscreen lists/report sections — never on active dialogs,
  focus targets, or the selected panel.
- Replace inline width/height attributes with CSS variables/data attributes so responsive CSS can override.

---

## 7. Effects & motion consolidation

- **Material/blur budget** (apply to glass generators, e.g. `glass_css_components.spl`): Navigation 8–10px /
  minimal shadow; Panel 12–14px / medium; Modal 16–18px / strong; reduced-transparency 0px / solid.
  Never stack blurred ancestors; opaque baseline before any `@supports (backdrop-filter)` enhancement;
  no blur on large scrolling content.
- **Motion tokens** (`--ui-duration-{instant,fast,base,slow}`, `--ui-ease-{standard,emphasized}`); remove
  `transition: all` in favor of explicit property lists; animate `transform`/`opacity`/color, not layout.
- **Reduced/off modes**: honor `prefers-reduced-motion` and the existing `data-wm-motion`/energy/quiet
  controls — strip pan/scale/drift/loop, keep immediate opacity/color feedback. Provide a transparency-off
  solid baseline.
- *(Dropped: the "`.widget-menubar` sticky→relative" defect — not reproduced in current source;
  reconciliation §3/§8. Re-file with a captured build if it recurs.)*

---

## 8. TUI & TUI-web parity

- **TUI height bug (confirmed, reconciliation §2):** add
  `terminal_height_breakpoints() -> Breakpoints(compact_max: 24, regular_max: 40)` in `profile.spl` and
  branch the `tui` `v_bp` selection (in `compute_profile` and `ProfileResolver.update`) to it. Add ≥160-col
  **ultra-wide capability flag** (not a 4th class). Map the shell to 1/2/3-pane terminal layouts.
- **TUI-web (`src/app/ui.tui_web/html.spl`):** consume shared base tokens + viewport normalization (safe
  areas, dynamic viewport, density profiles, adaptive status placement) while keeping monospace cell
  geometry. Replace fixed 14px text / 24px status bar / centered scroller (`:47,:50,:48`) with token-driven,
  responsive values.

---

## 9. Sequencing

| Phase | Theme | Why this order |
| --- | --- | --- |
| **P0 — Parity & security** | viewport-fit/color-scheme/safe-area/`dvh`, `data-engine/shell/platform` attrs, **output escaping**, coarse-pointer sizing, boundary screenshots | Cheap, high-value, unblocks everything; escaping is a security fix |
| **P1 — Web adaptive shell** | wire AppBar/Nav/Workspace/Support/Status/Overlay through shipped scaffolds; desktop sidebar/rail + mobile bottom-nav/list-detail; **no container queries** | Closes the real "morphology" gap by reusing native scaffolds |
| **P2 — Semantic widgets & a11y** | buttons/inputs/roles, keyboard models, native `<dialog>`/Popover, labels, live regions | Depends on stable shell DOM from P1 |
| **P3 — Effects & motion** | material/blur budget, motion tokens, reduced/off baselines | Independent; can parallelize with P2 |
| **P4 — TUI parity** | `terminal_height_breakpoints()`, ultra-wide flag, TUI-web tokenization | Independent track |
| **P5 — Quality gates** | extend existing structural-layout/screenshot/geometry/pixel gates to the new boundaries & states | Validation layer; reuse, don't rebuild |

P0 and P4 can start immediately and in parallel; P1 precedes P2; P3 is independent.

---

## 10. Acceptance matrix (extends existing gates)

- **Boundaries:** 599/600, 839/840, 1199/1200 width; height <480 landscape.
- **Devices:** 390×844, 430×932, 768×1024, 1024×768, 1280×800, 1440×900.
- **Engines/shells:** Electron (Chromium), Tauri WebKitGTK, real Safari/WKWebView, Android WebView, Simple
  in-house browser (fallback paths).
- **Conditions:** 200% zoom, enlarged text, keyboard-only, touch, dark/light, reduced motion, forced
  colors, transparency-off.
- **Invariants:** coarse-pointer targets ≥44px; focus never obscured by title bar / bottom nav / sheet;
  escaped output (injection test passes); pixel-parity gate green across engines with **zero blur tolerance**
  (matching current `gui_web_renderer_parity_hardening` discipline).

---

## 11. Open inputs

- The note's Instagram visual-token references could not be retrieved; **no colors/geometry were invented**.
  Attach screenshots if a precise visual-token mapping is wanted.
- The external CSS package (`simple-ui-adaptive-css.zip`) was not delivered; the layered file structure it
  proposes (`00-normalize` … `91-chromium`, plus flattened builds) is a **reference layering** to fold into
  the existing `generate_css(theme)` pipeline — adopt the normalize layer + small WebKit/Chromium override
  files, not a parallel build system.

---

## 12. Concrete Web WM evidence slice

This implementation slice advances the Web WM shell from static contract
coverage to repeatable Electron evidence. It does not claim the full typed UI
core migration, native SimpleOS WM parity, or RenderDoc/Vulkan parity.

**Current evidence:**
- `doc/01_research/ui/protocol/ui_modernization_plan.md` defines the broader typed UI core migration.
- `doc/01_research/ui/wm/simple_wm_modernization_local.md` records the generated CSS, preview HTML,
  runtime hooks, and focused unit contract.
- `test/01_unit/app/ui/web_wm_modern_shell_spec.spl` remains the low-dependency static contract.

**Acceptance criteria:**
- AC-1: The evidence wrapper records the generated preview, DOM audit JSON, ARGB JSON, PNG bitmap,
  interaction JSON, and post-interaction PNG under `build/test-artifacts/...`.
- AC-2: The wrapper validates contrast, target size, clipping, unexpected overlap, text containment,
  nonblank bitmap status, and Electron-delivered focus/keyboard/pointer/click events.
- AC-3: Hosts without Electron, Chromium backing, display support, or a working Simple runtime report
  `environment-unavailable` instead of passing placeholder assertions.
- AC-4: The generated/manual docs and process skills name the rendering and interaction evidence gates.
- AC-5: The interaction artifact proves real Chromium event delivery on the static preview. Full
  WebSocket-backed app action semantics remain a later gate.

**Canonical files:**
- `scripts/check/check-web-wm-modern-shell-evidence.shs`
- `tools/electron-live-bitmap/interact_html_controls.js`
- `test/02_integration/app/ui/web_wm_modern_shell_evidence_spec.spl`
- `doc/06_spec/02_integration/app/ui/web_wm_modern_shell_evidence_spec.md`
- `doc/07_guide/app/ui/web_wm_modern_shell.md`

**Focused verification:**

```bash
src/compiler_rust/target/release/simple test test/01_unit/app/ui/web_wm_modern_shell_spec.spl --mode=interpreter
sh scripts/check/check-web-wm-modern-shell-evidence.shs
src/compiler_rust/target/release/simple spipe-docgen test/02_integration/app/ui/web_wm_modern_shell_evidence_spec.spl --output doc/06_spec --no-index
src/compiler_rust/target/release/simple test test/02_integration/app/ui/web_wm_modern_shell_evidence_spec.spl --mode=interpreter --clean
```
