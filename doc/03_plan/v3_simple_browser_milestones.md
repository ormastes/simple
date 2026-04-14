# V3 Simple-Browser Milestones — Work Plan

**Date:** 2026-04-14
**Status:** Draft plan, derived from the V3 shell decision
**Source of truth:** `doc/01_research/domain/v3_shell_choice_2026-04-14.md`
**Plan item this unblocks:** `doc/03_plan/gui_drawing_layer_variations.md` §V3 (item 5)

---

## 0. Preamble

The T2 research doc `doc/01_research/domain/v3_shell_choice_2026-04-14.md`
selected **Option B — grow `examples/browser` / `std.gc_async_mut.gpu.browser_engine`**
into the V3 host shell, rejecting CEF. That decision is final for this plan.
This document does *not* re-litigate it. It turns "grow simple_browser" into
a numbered, gated milestone list the implementation track can follow.

The decision rests on three facts that this plan inherits without re-checking:
(1) `src/os/compositor/browser_compositor_backend.spl:11` already drives the
`widget → DOM → layout → paint → scene → buffer` pipeline against
`std.gc_async_mut.gpu.browser_engine`, (2) there are zero CEF references in
the tree, (3) `CLAUDE.md` mandates `.spl`/`.shs` for all code and a CEF
binding violates that. Five gates (M1–M5) in §6 of the T2 doc were derived
from V3 needs, not from a pre-existing milestone file inside
`examples/browser/`. This plan extends them to twelve numbered milestones
(M1–M12) covering V3 prerequisites and the immediate post-V3 work.

---

## 1. Current state snapshot

### 1.1 Directory layout (two levels)

`examples/browser/` (top-level files: `mod.spl`, `render_adapter.spl`,
`ui_bridge.spl`, `devtools_panel.spl`, `smoke_test.spl`,
`capsule.sdn`, `config.sdn`, `permissions.sdn`, `sandbox.sdn`):

```
examples/browser/
├── entity/{browser, dom, ipc, media, net, script}/
├── feature/{browser, composite, dom, gpu, layout, net, paint,
│            parser, sandbox, script, style}/
│         script/{builtins, engine, web_api}/
├── shared/
├── test/{architecture, compat, composite, dom, integration, ipc,
│          layout, net, paint, parser, reftest, script, style}/
└── transform/
```

`src/lib/gc_async_mut/gpu/browser_engine/` (flat — 13 files, no
subdirectories):

```
mod.spl, dom.spl, css.spl, layout.spl, paint.spl, widget_to_dom.spl,
style_block.spl, browser_renderer.spl, browser_engine2d_bridge.spl,
backend_screenshot_capture.spl, glass_comparison_runner.spl,
glass_pipeline_compare.spl, glass_demo_registry.spl
```

### 1.2 LOC by area

Counts via `wc -l` over `*.spl` (cited from the indexed batch run, label
`loc_examples_browser`, `loc_browser_engine`, `loc_per_module_browser`,
`loc_per_engine_module`):

| Area | Lines |
|------|-------|
| `examples/browser/` (total) | **62,142** |
| ↳ `feature/` | 45,711 |
| ↳ `test/` | 10,827 |
| ↳ `transform/` | 2,099 |
| ↳ `entity/` | 1,136 |
| ↳ `shared/` | 786 |
| `src/lib/gc_async_mut/gpu/browser_engine/` (total) | **5,993** |
| ↳ `dom.spl` | 1,508 |
| ↳ `browser_renderer.spl` | 869 |
| ↳ `layout.spl` | 863 |
| ↳ `widget_to_dom.spl` | 622 |
| ↳ `style_block.spl` | 516 |
| ↳ `css.spl` | 450 |
| ↳ `paint.spl` | 320 |
| **Combined** | **68,135** |

> Note: the T2 doc cited `examples/browser` at 62,760 lines (its own count).
> The 62,142 here is from a fresh `find ... | xargs wc -l` in the batch.
> The discrepancy is ≈600 lines and is consistent with files added/removed
> between 04-08 and 04-14.

### 1.3 WPT compatibility (2026-04-08 baseline)

Source: `examples/browser/test/compat/external/wpt_compatibility_report.md`.

| Category | Tests | Supported | Score |
|----------|-------|-----------|-------|
| Flexbox | 18 | 10 | **55.6%** |
| Colors | 10 | 3 | **30.0%** |
| Display | 5 | 0 | **0.0%** |
| Backgrounds | 5 | 1 | 20.0% |
| Positioning | 5 | 1 | 20.0% |
| Normal Flow | 2 | 0 | 0.0% |
| Floats | 5 | 0 | 0.0% |
| Acid1 / Acid2 | 2 | 0 | 0.0% |
| **Overall** | **37** | **14** | **37.8%** |

Most-needed missing features (top 5): `float/clear` (12 tests),
`hsl()/hsla()` (4), `display: contents` (3), `display: flow-root` (2),
`currentColor` (3).

### 1.4 The two-engines problem

`examples/browser/feature/{dom,style,layout,paint,parser}/...` (~45.7k
lines) and `src/lib/gc_async_mut/gpu/browser_engine/*.spl` (~6k lines) are
**parallel implementations** of overlapping subsystems. The compositor
wiring at `src/os/compositor/browser_compositor_backend.spl:11` only
imports the `std.` engine. T2 §7 flagged this as the M4 merge decision —
this plan resolves it in §3 below and assigns ownership to **M4**.

### 1.5 TODO/FIXME density

`grep -rE 'TODO|FIXME' examples/browser --include='*.spl'` returns **0**
matches (label `todo_total`). Either the team has been disciplined about
deleting them or stub markers are written differently; the
`code-style.md` rule ("never convert TODO to NOTE — implement or delete")
suggests the former. Treat the lack of TODOs as informational; missing
features still need to be inferred from the WPT report rather than from
inline markers.

---

## 2. Milestones M1 – M12

**Convention.** Each milestone has Goal / Acceptance / Unlocks / V3 gate /
Effort. Effort is T-shirt: **S** (≤1 week), **M** (1–3 weeks), **L** (1–2
months), **XL** (≥2 months). All milestones beyond M5 are speculative
extensions; M1–M5 are the gates the T2 doc itself derived from V3 needs.

### M1 — `ui.chromium/main.spl` skeleton

- **Goal.** Stand up a `src/app/ui.chromium/main.spl` that owns one winit
  window and presents pixels produced by `browser_compositor_backend`.
- **Acceptance criteria.**
  - [ ] `src/app/ui.chromium/{main,app,backend}.spl` exist and compile.
  - [ ] `bin/simple run examples/simple_os/desktop_shell --backend chromium`
        opens a window showing the existing taskbar.
  - [ ] Pixel path uses `rt_winit_buffer_create` + `present_rgba` only —
        no new FFI surface.
  - [ ] Window close is clean (no orphan threads).
  - [ ] No interactivity required.
- **Unlocks.** M2, M5.
- **V3 gate?** **YES.**
- **Effort.** **M.**

### M2 — Input event bridge

- **Goal.** Translate winit keyboard/mouse events into both
  `examples/browser/entity/dom/event_types.spl` DOM events and
  `common.ui.event` events.
- **Acceptance criteria.**
  - [ ] New `src/app/ui.chromium/event_bridge.spl` (mirrors
        `src/app/ui.browser/event_bridge.spl`).
  - [ ] `test/sys/wm_compare/input_event_chromium_spec.spl` passes the
        same input cases the PS/2 and hosted backends pass.
  - [ ] Modifier keys (shift/ctrl/alt/super) round-trip.
  - [ ] Mouse wheel → `wheel` DOM event.
  - [ ] No regressions in existing wm_compare input specs.
- **Unlocks.** M5, M9.
- **V3 gate?** **YES.**
- **Effort.** **M.**

### M3 — DesktopShell-subset CSS coverage

- **Goal.** Close the CSS gaps that the `DesktopShell` widget tree and the
  dark/light theme constants in `browser_compositor_backend.spl` actually
  exercise. **Not** a general WPT push.
- **Acceptance criteria.**
  - [x] Audit list of CSS properties produced by `widget_to_dom` for the
        `DesktopShell` tree, checked into the milestone ticket (see
        §M3 audit table below).
  - [ ] WPT score ≥80% on **Flexbox** (currently 55.6%). _Code-level
        features landed; WPT numeric gate re-measured by M5._
  - [ ] WPT score ≥60% on **Colors** (currently 30%). _Code-level
        features landed; WPT numeric gate re-measured by M5._
  - [x] `display: flow-root` and `display: contents` either implemented
        or explicitly waived as "not used by DesktopShell" — **waived**:
        `widget_to_dom` / `apply_glass_theme_styles` only emit
        `display: flex`, `display: grid`, and `display: none`. Neither
        `flow-root` nor `contents` appears anywhere in the DesktopShell
        widget tree or the theme constants in
        `browser_compositor_backend.spl`. `be_dom_set_style` still
        accepts them as freeform values (smoke-tested in
        `test/unit/app/ui.chromium/css_spec.spl`) so future widgets
        that set them won't panic, but the layout engine intentionally
        treats them as plain block boxes.
  - [x] `style_block.spl` expands `flex-flow` shorthand
        (`expand_flex_flow` — already present, now `pub` for tests).
  - [x] `currentColor` keyword works — `border-color: currentColor`
        resolves to the element's own `color` in `dom.set_style`
        (lines around the `border-color` arm).
  - [x] `hsl()/hsla()` parser added — `parse_hsl_func` in `dom.spl`,
        routed from `parse_color_value` (now `pub`).
- **Unlocks.** M5, M8.
- **V3 gate?** **YES.**
- **Effort.** **L.** (Speculative — derived from WPT report, not from a
  product-side requirements doc.)

#### M3 audit — CSS properties emitted for DesktopShell

The audit was produced by reading every `dom.set_style(...)` call in
`src/lib/gc_async_mut/gpu/browser_engine/widget_to_dom.spl`
(`apply_widget_props`, `ui_tree_to_dom`, `apply_glass_theme_styles`) and
walking the glass-theme branches that `DesktopShell` actually reaches.
DesktopShell renders through the `panel`, `card`, `button`, `heading`,
`label`, `text`, `menubar`, `statusbar`, `navigation_bar`, and
`divider` widget kinds, all of which fall through to
`apply_glass_theme_styles`.

| Property            | Emitted by                                           | Values observed                                       | Engine status                                                    |
|---------------------|------------------------------------------------------|-------------------------------------------------------|------------------------------------------------------------------|
| `display`           | `apply_widget_props`, `ui_tree_to_dom`               | `flex`, `grid`, `none`                                | OK — `layout_node` dispatches `flex`/`none`; others → block.     |
| `flex-direction`    | `apply_widget_props`, `ui_tree_to_dom`               | `row`, `column`                                        | OK — `layout_flex`.                                              |
| `gap`               | `apply_widget_props`                                 | px length                                              | OK — resolves via `parse_css_value`.                             |
| `width`, `height`   | `apply_widget_props`, `ui_tree_to_dom`               | px, %, `auto`                                          | OK — `CssValue.resolve_px`.                                      |
| `padding`           | `apply_glass_theme_styles`                           | `4px`, `8px`, `10px`                                    | OK — `BoxEdges` uniform.                                         |
| `color`             | `apply_glass_theme_styles`                           | `#F5F5F7`, `#1D1D1F`, hex with alpha                   | OK — `parse_color_value`.                                        |
| `background-color`  | `apply_widget_props`, `apply_glass_theme_styles`     | `#0A0A0F`, `#F0F0F5`, `rgba(...)`                      | OK — `parse_color_value` + unified `rgb`/`rgba` parser.          |
| `border-color`      | `apply_glass_theme_styles`                           | `rgba(255,255,255,0.08)`, `rgba(0,0,0,0.08)`           | OK — also honors `currentColor`.                                 |
| `border-width`      | `apply_glass_theme_styles`                           | `1px`                                                  | OK — `set_style` branch.                                         |
| `border-radius`     | `apply_glass_theme_styles`                           | `12px`, `16px`, `18px`, `20px`, `22px`                 | OK — `set_style` branch.                                         |

The theme constants exercised by `browser_compositor_backend.spl`
(`bg`, `fg`, `border_color`, `accent`, `panel_bg`, `hover_bg`,
`dim_fg`, `surface_bg`) are all plain hex or `rgba(...)` forms — no
`hsl()` and no `currentColor` appear in the DesktopShell emission
path. `hsl()/hsla()` and `currentColor` are still required by the
numeric WPT Colors gate, which is why they're kept as acceptance items
above; the code paths exist and are smoke-tested by
`test/unit/app/ui.chromium/css_spec.spl`.

- **M3 status (2026-04-14).** All code-level acceptance items
  implemented; numeric WPT gates to be re-measured under M5. Spec:
  `test/unit/app/ui.chromium/css_spec.spl` (compile-only smoke).

### M4 — Pick canonical engine and merge

- **Goal.** Eliminate the `examples/browser/feature/...` vs.
  `src/lib/gc_async_mut/gpu/browser_engine/...` duplication so V3 has a
  single import graph.
- **Acceptance criteria.**
  - [ ] ADR file (`doc/02_adr/NNN-canonical-browser-engine.md`) names the
        winner (this plan recommends `src/lib/.../browser_engine/`; see §3).
  - [ ] Every `use` site under `src/os/compositor/` and `src/app/ui.*`
        resolves to the canonical path.
  - [ ] Files in the loser path are either deleted or moved under
        `examples/browser/feature/` as test fixtures / labs only.
  - [ ] No file in `src/lib/` imports from `examples/`.
  - [ ] Same widget tree paints byte-identical output before and after
        the move (`wm_compare` golden harness, ≤1% perceptual diff).
- **Unlocks.** M5, M6, M7.
- **V3 gate?** **YES.**
- **Effort.** **L.**

### M5 — V3 wm_compare parity gate

- **Goal.** Make the V3 path pass the same `wm_compare` golden-image
  gate that V1 (baremetal) and V2 (hosted) already pass.
- **Acceptance criteria.**
  - [ ] `src/app/wm_compare/` learns a `--backend chromium` mode.
  - [ ] Golden frames captured for `DesktopShell` start screen, taskbar,
        menu, and one open app window.
  - [ ] V3 frames diff ≤1% perceptual against V1 baremetal output (per
        the `gui_drawing_layer_variations.md` rule).
  - [ ] CI job (`test/sys/wm_compare/v3_chromium_spec.spl`) runs in the
        standard test pass.
- **Unlocks.** V3 ship; M11.
- **V3 gate?** **YES.** (Final gate.)
- **Effort.** **M.**

---

> **M6–M12 are post-V3.** They exist so the team has a runway, but they
> are **not** prerequisites for closing item 5 of
> `gui_drawing_layer_variations.md`. Each is "estimated from product
> direction, not from existing tickets."

### M6 — Multi-window / tabs

- **Goal.** Support more than one top-level window per process so the
  browser can host multiple `DesktopShell` instances or browser tabs.
- **Acceptance criteria.**
  - [ ] Window manager tracks N winit windows.
  - [ ] Per-window `RenderScene` and damage region.
  - [ ] Focus and z-order work between windows.
  - [ ] Shutdown of one window does not affect siblings.
- **Unlocks.** M9.
- **V3 gate?** NO.
- **Effort.** **M.**

### M7 — `engine2d` WebGPU path

- **Goal.** Add a GPU raster path so `browser_compositor_backend` is not
  the only option. Listed as a separate gap in
  `gui_drawing_layer_variations.md` §V3.
- **Acceptance criteria.**
  - [ ] `src/lib/gc_async_mut/gpu/engine2d/backend_webgpu.spl` exists.
  - [ ] Same scene → identical (≤1%) pixels vs. software backend.
  - [ ] FPS ≥ 2× software path on the `DesktopShell` benchmark.
- **Unlocks.** M10.
- **V3 gate?** NO. (Software path is sufficient for V3.)
- **Effort.** **L.**

### M8 — WPT >50% overall

- **Goal.** Push the overall WPT score past 50% (currently 37.8%) by
  finishing the high-impact missing features the report ranks #1–#10.
- **Acceptance criteria.**
  - [ ] `float/clear` implemented end-to-end.
  - [ ] `box-shadow` paint command.
  - [ ] `outline` paint.
  - [ ] `calc()` parser + resolver.
  - [ ] Overall WPT score ≥50%.
- **Unlocks.** M12.
- **V3 gate?** NO.
- **Effort.** **XL.**

### M9 — JS engine maturity audit

- **Goal.** Honest assessment of `examples/browser/feature/script/engine/`
  against ECMAScript conformance test262.
- **Acceptance criteria.**
  - [ ] test262 runner wired (subset OK).
  - [ ] Pass-rate report checked in.
  - [ ] Clear list of "things V3 apps will hit and crash on."
- **Unlocks.** Decision on whether to keep the JIT or rip it out.
- **V3 gate?** NO. (V3 itself does not run JS.)
- **Effort.** **L.**

### M10 — DevTools attach

- **Goal.** Surface `examples/browser/devtools_panel.spl` against a live
  `DesktopShell` window for debugging V3 paint issues.
- **Acceptance criteria.**
  - [ ] DevTools panel renders the live DOM tree.
  - [ ] CSS inspector shows computed styles.
  - [ ] No requirement for Chrome DevTools Protocol parity.
- **Unlocks.** Faster M3 / M8 iteration.
- **V3 gate?** NO.
- **Effort.** **M.**

### M11 — Snapshot / record-replay test mode

- **Goal.** Capture a deterministic frame-by-frame log of a V3 session so
  visual regressions can be triaged offline.
- **Acceptance criteria.**
  - [ ] `--record session.bin` flag on `ui.chromium`.
  - [ ] Replay produces byte-identical frames.
  - [ ] Used by ≥1 wm_compare regression test.
- **Unlocks.** Confidence in M3/M8 changes.
- **V3 gate?** NO.
- **Effort.** **S.**

### M12 — Acid2 pass

- **Goal.** Acid2 reftest (currently UNSUPPORTED) passes.
- **Acceptance criteria.**
  - [ ] Acid2 reftest in WPT report flips to SUPPORTED.
  - [ ] No regressions in DesktopShell golden frames.
- **Unlocks.** Marketing milestone — "simple_browser is real".
- **V3 gate?** NO.
- **Effort.** **L.**

---

## 3. V3 prerequisite set

To ship a usable V3 row in `gui_drawing_layer_variations.md`, the
following must be done: **{ M1, M2, M3, M4, M5 }**. Everything else is
post-V3 enhancement. M5 is the final gate (the wm_compare parity check),
so V3 is "done" the moment M5 is green.

| Milestone | V3 gate? | Blocks V3 because |
|-----------|---------|-------------------|
| M1 | YES | No window means no V3 row. |
| M2 | YES | No input means no parity with V1/V2 input specs. |
| M3 | YES | DesktopShell skin breaks without the CSS subset. |
| M4 | YES | A second engine path means non-deterministic V3. |
| M5 | YES | Parity gate is the definition of "V3 ships". |
| M6–M12 | NO | Useful, not blocking. |

---

## 4. Merge-the-two-engines plan (owns: M4)

### 4.1 Why duplication exists (best guess from code)

`examples/browser/feature/...` looks like the maximalist
"Chromium-class browser" project (62k LOC, has `script/engine/jit.spl`,
`net/h2_client.spl`, `sandbox/`, etc.). It is internally consistent and
has its own test tree under `examples/browser/test/`.

`src/lib/gc_async_mut/gpu/browser_engine/` (6k LOC) looks like the
**minimum viable engine** that was carved out so
`src/os/compositor/browser_compositor_backend.spl:11` could `use std.…`
without dragging in 60k lines of unrelated browser code. It has only the
modules needed for `widget_to_dom → layout → paint → scene`. Confirmed
by `compositor_backend_imports`:

```
11: use os.compositor.display_backend.{CompositorBackend}
    use std.gc_async_mut.gpu.browser_engine.{dom, css, layout, paint,
                                             widget_to_dom}
```

Best guess: the `std.` engine was extracted as a slimmed-down dependency
for `os/compositor/`, and `examples/browser/feature/...` evolved
independently as the full browser. Nobody has reconciled them since.

### 4.2 Recommended canonical target

**`src/lib/gc_async_mut/gpu/browser_engine/`** is the canonical V3 engine.

Reasons:
1. It is what the compositor already imports — zero rewiring cost.
2. It is small (6k LOC) and review-able as a unit.
3. `examples/` is by repo convention non-load-bearing; pulling load-bearing
   code out of `examples/` aligns with `structure.md`.
4. `CLAUDE.md` says `use std.X` resolves under `src/lib/` — the canonical
   import shape is already `std.gc_async_mut.gpu.browser_engine`.

`examples/browser/feature/...` should be retained as a **feature lab**:
test fixtures, JS engine experimentation, networking lab, sandbox lab.
Nothing in `src/` may import from it.

### 4.3 Stepwise merge plan

1. Freeze API of `std.gc_async_mut.gpu.browser_engine.{dom,css,layout,paint,widget_to_dom}`.
2. Diff each `examples/browser/feature/{dom,style,layout,paint}/` file
   against the `std.` counterpart. For each divergence:
   - If `std.` is missing a feature → port it into `std.`.
   - If `examples/` is missing a feature → leave it alone.
3. Once `std.` is a strict superset of what V3 needs, change every `use`
   site under `src/` to import only from `std.`.
4. Move `examples/browser/feature/{dom,style,layout,paint}/` aside or
   delete; keep `examples/browser/feature/{net,script,sandbox}/` as the
   lab (V3 doesn't need them).
5. Write the ADR (`doc/02_adr/NNN-canonical-browser-engine.md`).
6. Run `wm_compare` golden gate before/after to prove no pixel drift.

### 4.4 Owner

**M4** owns this. Cannot start before M1 (the merge needs the V3 entry
point so we know which symbols are load-bearing). Should land **before**
M5 so the parity gate measures the canonical engine.

---

## 5. Out of scope

V3 is "the same `DesktopShell` apps run inside a windowed simple_browser
and pass the wm_compare golden gate." Nothing more. Explicitly out of
scope for this plan:

- JS JIT maturity (`feature/script/engine/jit.spl`) — V3 doesn't run JS.
- DevTools polish beyond M10's "attach to live window".
- WebGPU beyond M7 (post-V3).
- Network stack (`feature/net/...`) beyond what `DesktopShell` already needs.
- Browser extensions / WebExtensions API.
- Service workers, PWAs, manifest handling.
- Media pipeline (audio/video codecs, MSE/EME).
- Site isolation / multi-process beyond a single renderer.
- Acid3, WebRTC, WebGL, Canvas2D conformance.
- Font shaping beyond what `widget_to_dom` already does.

These all live in `examples/browser/feature/...` and stay there as labs.

---

## 6. Dependencies on other tracks

| Track | Question | Status / answer |
|-------|----------|-----------------|
| **T1** — `CompositorBackend` contract | Does V3 need any methods that aren't on the trait today? | **Unknown.** `src/os/compositor/browser_compositor_backend.spl` already implements the trait. M1 must verify the winit-driven version doesn't need new trait methods. Track as M1 acceptance check. |
| **T3** — hosted_backend rewire | Does V3 depend on T3 landing first? | **No.** V3 has its own backend (`browser_compositor_backend`) and does not share code with `hosted_backend.spl`. T3 can ship in either order. |
| **T7** — `wm_compare` parity harness | When does V3 join the harness? | **At M5.** M5's acceptance is "V3 frames diff ≤1% against V1." T7 must already export a `--backend chromium` shape by then; if not, M5 grows a sub-task to add it. |
| **T2** — research doc | Already landed (`doc/01_research/domain/v3_shell_choice_2026-04-14.md`). | This plan is its successor. |

---

## 7. Open questions

These cannot be resolved without a product / architecture decision and
are deliberately not assigned to any milestone:

1. **Is `examples/browser/feature/script/engine/` the long-term JS
   strategy, or a placeholder?** M9 audits it; the answer determines
   whether V4-class apps (which *do* run JS) can also use simple_browser
   or whether they need V4 (Electron) forever.
2. **Sandbox model.** `examples/browser/feature/sandbox/` exists but the
   compositor side has no process boundary today. V3 doesn't need
   site isolation; V4-class apps will. Decide before M6.
3. **GPU compositor responsibility.** Does `engine2d` own the WebGPU
   path, or does `browser_engine/` get its own GPU rasterizer? Decide
   before M7.
4. **`examples/browser/`'s "12-milestone" memory note has no on-disk
   counterpart.** Either rewrite the note to point at this file, or
   recover the original list and merge it. Right now they conflict.
5. **WPT regression policy.** If a V3-driven CSS change breaks a WPT
   test outside the DesktopShell subset, do we revert or accept? M3
   needs an answer.
6. **Should `src/app/ui.browser/` and `src/app/ui.chromium/` merge?**
   They overlap conceptually. Decide before M5 or live with two adapters
   forever.

---

## 8. Cross-references

- `doc/01_research/domain/v3_shell_choice_2026-04-14.md` — decision.
- `doc/03_plan/gui_drawing_layer_variations.md` — V3 row, item 5.
- `doc/04_architecture/cross_platform_wm.md` — winit FFI surface
  (`rt_winit_buffer_create`, `present_rgba`).
- `src/os/compositor/browser_compositor_backend.spl:11` — the
  integration point; already imports `std.gc_async_mut.gpu.browser_engine.*`.
- `src/os/compositor/browser_backend.spl` — sibling render backend
  documenting the `widget_to_dom → layout → paint → scene → buffer`
  pipeline.
- `examples/browser/test/compat/external/wpt_compatibility_report.md` —
  conformance baseline (2026-04-08).
- `examples/browser/mod.spl` — entry point for the in-tree browser
  (multi-process model description).
- `examples/browser/render_adapter.spl`, `ui_bridge.spl`,
  `devtools_panel.spl`, `smoke_test.spl` — existing app-side scaffolding
  M1 will mirror under `src/app/ui.chromium/`.

