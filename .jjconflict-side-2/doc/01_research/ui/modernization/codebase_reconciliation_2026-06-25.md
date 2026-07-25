# Deep Research — External UI-Modernization Note vs. Simple Codebase (Reconciliation)

**Date:** 2026-06-25
**Phase:** 01_research / ui / modernization
**Purpose:** Verify, claim-by-claim and against the actual source, the external
"Simple UI modernization" note ([external_ui_modernization_research_2026-06-25.md](./external_ui_modernization_research_2026-06-25.md)).
Establish what is **true now**, what the note got **wrong or stale**, and what is **already shipped**, so the
plan ([../../../03_plan/ui/modernization/ui_modernization_plan_2026-06-25.md](../../../03_plan/ui/modernization/ui_modernization_plan_2026-06-25.md))
acts only on real, current gaps.

**Method:** four independent source-reading passes (layout model, CSS, HTML semantics, existing-plan
survey). Every verdict below is backed by file:line evidence in the current working tree
(branch `main`, synced to `origin/main` @ `7a49542470`, 2026-06-25).

---

## 0. Executive summary

The note's **web/HTML-renderer findings are largely correct** — the renderer emits non-semantic
markup (`<span>`/`<div>` controls), minimal viewport metadata, and unescaped interpolation. Its
**central TUI bug is real and well-diagnosed**. But its **layout-morphology framing is stale**: the
"missing" bottom-nav→rail→sidebar transformation, list/detail model, and two-axis size classes
were **shipped** in SPipe `mobile-gui-platform` (2026-06-13). And at least one **concrete "defect"
it cites does not reproduce** in the current source.

Net: adopt the note's **accessibility + browser-parity + TUI-height** recommendations; **down-scope**
its adaptive-shell section to "wire the *web renderer* into the already-shipped scaffold model"; and
**reject** its container-query dependency (the in-house CSS parser deliberately does not implement
`@container`).

| Theme | Note's claim | Verdict | Action |
| --- | --- | --- | --- |
| Two-axis size classes 600/840 + 480/900 | "right foundation" | ✅ CONFIRMED & shipped | Keep; no work |
| TUI rows reuse 80/160 col thresholds | bug | ✅ CONFIRMED (real) | **Fix** (P-TUI) |
| Tabs/checkbox/radio/pills are span/div | non-semantic | ✅ CONFIRMED | **Fix** (P-A11y) |
| Viewport meta minimal | true | ✅ CONFIRMED | **Fix** (P-Parity) |
| Unescaped interpolation | injection risk | ✅ CONFIRMED (escaper exists, unused) | **Fix** (P-Parity, security) |
| `simple_default.css` centers body | true | ✅ CONFIRMED | Keep theme for docs; don't reuse as shell |
| TUI-web fixed 14px/24px, no safe-area | true | ✅ CONFIRMED | **Fix** (P-TUI-web) |
| `.widget-menubar` sticky→relative defect | bug | ❌ **NOT REPRODUCED** | Drop from plan; verify before citing |
| Tablet = "two-column grid" | gap | ⚠️ MISLEADING | Reality: collapses to 1-col @768px; scaffolds already exist natively |
| "No rail→sidebar / list-detail / supporting-pane" | gap | ⚠️ STALE | Shipped natively; **only the web renderer lacks wiring** |
| Use container queries | recommendation | ⛔ CONFLICTS | Parser omits `@container` by design; use scaffolds + `@media` |

---

## 1. Adaptive layout model — CONFIRMED, and richer than the note implies

All four foundational claims verify exactly:

- **GUI width classes 600 / 840** — `src/lib/common/ui/profile.spl:50-56`, `default_breakpoints() → Breakpoints(compact_max: 600, regular_max: 840)`; comment "Material-aligned 600/840". `classify()` thresholds at `profile.spl:81-88`.
- **GUI height classes 480 / 900** — `profile.spl:58-62`, `height_breakpoints() → Breakpoints(compact_max: 480, regular_max: 900)`.
- **Terminal width 80 / 160 columns** — `profile.spl:64-66`, `terminal_breakpoints() → Breakpoints(compact_max: 80, regular_max: 160)`.
- **`LayoutProfile` records both axes + orientation** — `profile.spl:100-105`: fields `horizontal`, `vertical`, `orientation`, `width`, `height`.

**What the note misses:** the model is already operationalized beyond raw breakpoints.
SPipe `mobile-gui-platform` (status: shipped, 2026-06-13) added:

- `src/lib/common/ui/form_factor.spl` — `DeviceClass {Phone|Tablet|Desktop}`, `FormFactorProfile`, `detect_device_class()`; touch-target floor (44pt Apple / 48dp other / ~32px dense desktop), hover, density tokens.
- `src/lib/common/ui/adaptive_scaffold.spl` — **`adaptive_nav_scaffold()`** (bottom bar → nav rail → sidebar) and **`list_detail_scaffold()`** (two panes ≥840dp, single pane + push nav below).
- Specs green: form_factor 29/29, adaptive_scaffold 14/14, responsive_css_parity 6/6.

→ The note's section 2 ("no complete bottom-navigation → rail → sidebar transformation, no list/detail
state model") is **true only of the HTML web renderer's *generated CSS*** — not of the native layout
engine, where these patterns exist. The plan reframes this as a **wiring gap**, not a design gap.

---

## 2. TUI vertical classification — BUG CONFIRMED (note is correct)

The note's most important technical finding is **real**:

- There is **no** `terminal_height_breakpoints()` anywhere in `src/` (verified by grep).
- `profile.spl:107-123` (`compute_profile`) and `profile.spl:234-250` (`ProfileResolver.update`) both do:
  ```spl
  val v_bp = if viewport.active_backend == "tui":
      terminal_breakpoints()      # <- 80/160 reused for HEIGHT (rows)
  else:
      height_breakpoints()
  ```
- Consequence: a normal **80×24** terminal classifies as height-Compact (24 < 80); **120×40** also
  height-Compact (40 < 80). Vertical class is effectively always Compact for realistic terminals.

**Fix** (adopt the note's shape, refined): add `terminal_height_breakpoints() → Breakpoints(compact_max: 24, regular_max: 40)` and branch the `v_bp` selection to it for the `tui` backend. Treat ≥160 columns as an **ultra-wide capability flag**, not a 4th global size class (consistent with the existing 3-class `SizeClass`).

---

## 3. CSS claims — mostly CONFIRMED, one defect NOT reproduced

- **`simple_default.css` centers the body** — ✅ `src/lib/common/ui/theme_html/simple_default.css:62-72`: `body { max-width: 80rem; margin-left:auto; margin-right:auto; }`. The note's guidance to keep this theme for documents (not the app shell) is sound.
- **Universal box-sizing omits pseudo-elements** — ✅ literally (`simple_default.css:53-55` is `* { box-sizing: border-box; }`, no explicit `::before,::after`). **Nuance:** in modern engines `*` already matches pseudo-elements, so this is cosmetic, not a real bug. Low priority.
- **Compact rules (44px / 16px / 1-col / hidden sidebar)** — ⚠️ PARTIAL. 16px and dynamic grid columns exist (`src/app/ui.render/html.spl:136,167,275`); the responsive collapse to one column is at `src/app/ui.render/css.spl:214-222` (`@media (max-width:768px){.card-grid{grid-template-columns:1fr}}`). **No explicit 44px touch-target rule and no `display:none` sidebar** were found in the generated CSS (the 44pt floor lives as *policy* in `form_factor.spl`, not as emitted CSS).
- **Tablet = "two-column grid"** — ❌ MISLEADING. The only breakpoint in `css.spl:214-222` *collapses to one column* at ≤768px; there is no two-column tablet grid in the generated CSS at all. The note over-describes the current state.
- **`.widget-menubar` sticky→relative defect** — ❌ **NOT REPRODUCED.** `src/lib/common/ui/glass_css_components.spl:70-78` sets `.widget-navigation-bar, .widget-menubar { … position: sticky; top:0; z-index:100; }`. The only *other* mention of `.widget-menubar` is `glass_css_components.spl:463-465`, which sets `font-family` — **it does not set `position: relative`.** No second positioning rule cancels the sticky. **The cited defect appears stale or from a different artifact.** → Remove from the plan unless re-verified against a specific generated build.

---

## 4. HTML semantics — CONFIRMED (note is correct), main renderer is `html_widgets.spl`

The non-semantic markup lives in `src/app/ui.render/html_widgets.spl` (the note pointed at `ui.web/html.spl`; the actual widget emitters are in `ui.render`):

- **Tabs as `<span>`** — ✅ `html_widgets.spl:363` (`<span class="tab-item…" data-action=…>`).
- **Checkbox / radio as `<div>`** — ✅ `html_widgets.spl:393` (checkbox), `:410,:419` (radio) — nested `<div>` with custom marks, no `<input>`.
- **Div-based workspace tabs / rail / pills / context-menu** — ✅ `:660` (ws-tab), `:728` (rail-icon), `:750` (pill-item), `:704` (context-item).
- **Missing ARIA** — ✅ no `aria-selected` / `aria-controls` / `aria-expanded` / `role="tablist"` / roving tabindex; tree tracks `expanded` state (`:178`) without exposing it. Keyboard tab-switch is click-only (`src/app/ui.web/html.spl:2272-2287`), no arrow keys.
- **Viewport meta minimal** — ✅ `src/app/ui.web/html.spl:45` and `src/app/ui.tui_web/html.spl:27` both emit only `width=device-width, initial-scale=1.0` (no `viewport-fit=cover`, no `color-scheme`).
- **Unescaped interpolation** — ✅ with a sharp twist: an `html_escape()` helper **exists** at `src/app/ui.render/html.spl:11-19` but is **not used** in `html_widgets.spl`. Properties are concatenated raw at `:384,:393,:410,:419,:446,:451,:461` (labels, titles, `value`, `placeholder`, `src`, `alt`, `data-action`). This is a **real injection vector** for any user-controlled widget content — flag as security, not just a11y.
- **TUI-web minimal surface** — ✅ `src/app/ui.tui_web/html.spl:47` (`font-size:14px`), `:50` (`#status-bar{height:24px;line-height:24px}`), `:48` (centered flex scroller); no safe-area, no dynamic viewport units, no density classes.

---

## 5. Where the note CONFLICTS with established repo direction

1. **Container queries (`@container`).** The note builds its component-adaptation story on container
   queries while hedging that "Simple's own CSS parser does not yet claim full modern CSS support."
   The repo position is **stronger and deliberate**: SPipe `m17-css3-completeness` (closed) measured CSS3
   coverage and **explicitly deferred `@container`**; `responsive_layout_platforms.md` records scaffolds
   as the chosen near-term mechanism. The in-house parser implements `@media`, `var()` across all blocks,
   flexbox, sticky, transforms/animations, and **partial `@supports`** (property queries + `not`; no
   `and`/`or`/`selector()`), but **no Grid and no `@container`**. → The plan must express adaptive
   components through the **scaffold API + `@media`**, treating container queries as Chrome/Safari-only
   progressive enhancement that **must never be required**.

2. **"Two complete themes will drift" / shared normalization layer.** Already the repo's model: a single
   `config/themes/theme.sdn` registry feeds one `generate_css(theme)` adapter shared by Electron/Chromium
   and Simple Web (`doc/02_requirements/ui/simple_theme_system.md`, shipped). The note's "one shared
   normalization + small engine overrides" is **aligned**, not new — adopt its *normalize layer + WebKit/
   Chromium override files* as a refinement *inside* the existing theme pipeline, not as a parallel system.

3. **Implementation order P0–P5.** The note's ordering assumes the adaptive shell is greenfield. Because
   the native scaffold + size-class + parity work is **already shipped/production**, the repo ordering is
   different (see plan): browser-parity + a11y + security first; "adaptive shell" reduces to wiring the web
   renderer into existing scaffolds; effects/motion consolidation and TUI height are independent tracks.

4. **Quality gates.** The note correctly says to **extend** existing infra rather than build a new audit
   system — the repo already has structural-layout SDN, screenshot, geometry, and pixel-parity gates
   (`harden_tui_gui_layout_comparison`, `gui_web_renderer_parity_hardening`: Electron/Tauri/Chrome 18/18,
   zero mismatch). This is alignment; reuse those gates.

---

## 6. Already-shipped work the plan must NOT redo (with sources)

| Capability | Status | Source |
| --- | --- | --- |
| Theme system, single source of truth, token↔CSS round-trip, live reload | shipped | `doc/02_requirements/ui/simple_theme_system.md`; `theme.sdn`; `app.ui.web.html.generate_css` |
| Two-axis size classes (600/840 + 480/900) + `DeviceClass` policy | shipped | `profile.spl`, `form_factor.spl` (SPipe `mobile-gui-platform`) |
| `adaptive_nav_scaffold()` (bottom→rail→sidebar) + `list_detail_scaffold()` | shipped | `adaptive_scaffold.spl` |
| Web/Tauri/Chrome pixel parity (18/18 each, zero blur tolerance) | production | `gui_web_renderer_parity_hardening`; `doc/03_plan/ui/web_browser/simple_browser_chromium_html_parity.md` |
| Server-authoritative WM + WSS patch protocol + capability gating | shipped | `web-wm-authoritative`; `doc/04_architecture/ui/simple_gui_stack.md` |
| UI Access Protocol (snapshots, MCP tools, visual probe) | shipped | `doc/02_requirements/ui/ui_access_protocol.md` |
| HTML/CSS toolchain (`ui-edit`, `ui-build`), theme element library (47 elements), verify oracle | shipped | `html_ui_toolchain`; `doc/07_guide/ui/html_ui/llm_html_ui_guide.md` |
| Partial `@supports` (property queries + `not`) | shipped | `m17-css3-completeness` (CSS parser) |
| Engine2D Metal/Vulkan/CPU-SIMD backends + measurement matrix | production | `doc/04_architecture/ui/engine_2d.md`; `harden_tui_gui_layout_comparison` |

---

## 7. Confirmed, current gaps the plan SHOULD act on

1. **Semantic + accessible widgets** in `html_widgets.spl`: real `<button role="tab">`/`role="tablist"`,
   native `<input type=checkbox|radio>` + `<label>`, buttons for pills/rail/menu/results; `aria-selected`,
   `aria-controls`, `aria-expanded`, `aria-sort`, roving tabindex, arrow-key navigation.
2. **Output escaping / injection hardening**: apply the existing `html_escape()` to every interpolated
   property in `html_widgets.spl`. (Security + correctness.)
3. **Browser-parity head metadata**: add `viewport-fit=cover`, `<meta name="color-scheme">`,
   `env(safe-area-inset-*)`, dynamic viewport units (`dvh`) where `100vh` is used; emit
   `data-engine`/`data-shell`/`data-platform` on `<html>` from the backend that already knows the shell.
3. **Web-renderer adaptive shell wiring**: express the AppBar/Nav/Workspace/Support/Status/Overlay regions
   through the **shipped scaffold API**, so the *generated CSS/HTML* gains the bottom-nav→rail→sidebar and
   list/detail morphology the native engine already has. No container queries.
4. **TUI height breakpoints**: add `terminal_height_breakpoints()` (24/40) and a ≥160-col ultra-wide flag.
5. **TUI-web parity**: consume shared base tokens + viewport normalization; safe-area, dynamic viewport,
   density profiles, adaptive status placement — keeping monospace cell geometry.
6. **Effects/motion consolidation**: material/blur budget, motion tokens, remove `transition: all`,
   `prefers-reduced-motion` + transparency-off baselines (Simple already exposes `data-wm-motion`/energy).
7. **Native `<dialog>` / Popover** paths for modals/menus with deterministic fallback for the in-house browser.

## 8. Items to DROP or verify before acting

- **`.widget-menubar` sticky→relative defect** — not reproduced in current source (§3). Do not include as
  a fix item; if it came from a generated build, capture that build and re-file with evidence.
- **"Tablet is a two-column grid"** — inaccurate; current generated CSS collapses to one column at 768px.
  Frame the work as "add real tablet morphology via scaffolds," not "replace a two-column grid."
- **Container-query-based component adaptation** — keep strictly as optional progressive enhancement.
