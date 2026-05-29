# V3 Shell Choice — CEF vs. simple_browser

**Date:** 2026-04-14
**Status:** Decision (unblocks `doc/03_plan/gui_drawing_layer_variations.md` item 5)
**Decision:** **Option B — grow `examples/browser` (simple_browser) into the V3 host shell.**

---

## 1. Problem statement

V3 in `doc/03_plan/gui_drawing_layer_variations.md` is "Pure Simple + Chromium
host (no Node)". The pipeline already exists on the Simple side:

```
App → common.ui.* → os.services.wm →
  os.compositor (browser_compositor_backend / browser_backend) →
  engine2d (backend_software → HTMLCanvas / WebGPU bridge) →
  <Chromium-class shell>
```

What is missing — and what V3 plan item 5 ("CEF or simple_browser shell driving
`browser_compositor_backend`") is gated on — is the actual shell that owns a
real OS window, runs a JS engine + DOM, and accepts the paint scenes our
`browser_compositor_backend` produces. Plan item 5's artifact is
`src/app/ui.chromium/main.spl` plus parity screenshots against V1/V2. This doc
picks which engine that `ui.chromium/main.spl` will drive.

## 2. Option A — CEF bindings via SFFI

CEF (Chromium Embedded Framework) is the canonical embeddable Chromium. Wrap
its C API (`cef_capi`) through Simple's SFFI (`.claude/memory/ref_sffi.md`) and
expose a thin `os.compositor.cef_backend` that hosts a CEF browser window,
ships paint scenes via shared memory or `OnPaint`, and forwards input events.

**What CEF buys us**
- Production-grade Blink layout, V8 JS, WebGPU, networking stack, DevTools,
  HiDPI, accessibility, print-preview, video/audio.
- All four host OSes covered (macOS, Windows, Linux, BSD via Chromium).
- Mature multi-process sandbox model.

**Costs and risks**
- A CEF distribution is ~150–300 MB per platform; shipping it cross-platform
  is its own release-engineering project.
- C API is large (>1000 functions) and version-locked to a Chromium release.
  Binding churn every 6 weeks. Each Simple release has to re-pin a CEF build.
- Repo audit: **zero CEF references today**. `grep -rE 'CEF|libcef|cef_capi'`
  returns nothing across `*.spl`, `*.rs`, `*.md`, `*.toml`. There is no
  partial work to build on.
- Violates the "ALL code in `.spl`" rule from `CLAUDE.md`. Even with the
  "implement in Simple unless big perf difference" carve-out, CEF is the
  exact opposite of the project posture: it makes V3 a thin viewer over
  someone else's renderer, defeating the point of "Pure Simple + Chromium".
- Licensing: CEF is BSD over LGPL/Apache Chromium — workable but adds an
  audit task we don't have today.
- Not "pure Simple". V3's title literally says "Pure Simple + Chromium host";
  the "+" was meant to be Chromium-class behaviour, not a binary blob.

## 3. Option B — grow `examples/browser` (simple_browser)

The repo already contains a substantial in-tree browser engine.

**What exists today**
- `examples/browser/` is real: top-level dirs `entity/`, `feature/`,
  `transform/`, `shared/`, `test/`, plus `mod.spl`, `render_adapter.spl`,
  `ui_bridge.spl`, `devtools_panel.spl`, `smoke_test.spl`.
- `wc -l` over `examples/browser/**/*.spl` reports **62,760 lines total**
  (`render_adapter.spl:514`, `ui_bridge.spl:450`, `devtools_panel.spl:378`,
  `mod.spl:191`, plus the entity/feature/transform/test tree).
- Subsystems already present as `.spl` files (`examples/browser/feature/...`):
  - **JS engine:** `script/engine/lexer.spl`, `parser.spl`,
    `bytecode_compiler.spl`, `interpreter.spl`, `vm.spl`, `jit.spl`, `gc.spl`,
    `runtime.spl`; builtins for `string/number/object/json/promise/date/error/
    typed_array`; web APIs `console_binding`, `fetch_binding`, `timer_binding`,
    `worker_binding`, `dom_bindings`, `event_binding`, `crypto_binding`.
  - **Networking:** `feature/net/{dns,tls,h1_client,h2_client,websocket_client,
    fetch,cors,cache,cookie_store}.spl`.
  - **Parser/DOM/style/layout/paint:** full HTML/CSS tokenizers, tree builder,
    selector matcher, cascade, computed style, flex/grid/inline/block/table/
    multicol/scroll/text-shape layout, paint commands, stacking, damage
    tracking — plus a sandbox tier (`sandbox/{site_isolation,
    capability_broker,csp}.spl`).
- A second engine lives at `src/lib/gc_async_mut/gpu/browser_engine/` (~5,993
  lines) and is the one `src/os/compositor/browser_compositor_backend.spl`
  already imports (`std.gc_async_mut.gpu.browser_engine.{dom,css,layout,paint,
  widget_to_dom}`). So the compositor-side wiring **already exists** — V3
  needs the shell, not the engine plumbing.
- Backend slots already scaffolded: `src/app/ui.browser/{app,backend,
  dom_bridge,event_bridge,renderer,main}.spl` and `src/app/ui.web/*` and
  `src/app/ui.electron/*`. There is **no** `src/app/ui.chromium/` yet — that
  is exactly the artifact plan item 5 demands.
- Conformance baseline is being measured: `examples/browser/test/compat/
  external/wpt_compatibility_report.md` (dated 2026-04-08) reports against 37
  WPT reftests + 2 Acid tests. Flexbox 55.6% supported, Colors 30%, Display
  0% supported. So we know honestly where the engine is.

**What "Chromium-class" actually has to mean for V3**
V3's job is *not* to be a daily-driver web browser. V3 must:
1. Open an OS window via the existing hosted backends (winit FFI is already
   in place — `cross_platform_wm.md` "Winit FFI Functions Used" lists
   `rt_winit_window_new`, `rt_winit_buffer_create`, `present_rgba` etc.).
2. Run the apps that the rest of `gui_drawing_layer_variations.md` cares
   about: a `DesktopShell`-style widget tree fed through
   `widget_to_dom → layout → paint → render_scene`.
3. Pass the same `wm_compare` golden-image gate that V1/V2/V4 pass
   (≤1% perceptual diff against V1 baremetal output).

That bar is **layout + paint + input + a small subset of CSS that the in-tree
widgets actually use** — not Acid3, not WebRTC, not video codecs. The existing
`browser_engine` already covers flex/grid/block/inline/text and a software
paint pipeline. The honest gap is finishing the `ui.chromium/main.spl`
wrapper, the input-event translation, and the missing CSS bits the
`DesktopShell` skin will exercise.

## 4. Decision criteria matrix

| Criterion                    | Option A: CEF | Option B: simple_browser |
|------------------------------|---------------|--------------------------|
| Effort to a usable V3        | high          | medium                   |
| "Pure Simple"-ness           | low           | high                     |
| Chromium feature parity      | high          | low (and OK — see §3)    |
| Maintenance burden           | high (CEF re-pin, large C ABI, multi-OS binaries) | medium (in-repo, our own bugs) |
| Unblocks other plan items    | only V3       | V3 + WPT work + ui.web + ui.electron share engine |
| Already exists in repo       | 0 LOC, 0 refs | ~62,760 LOC + 5,993 LOC engine, compositor wired |
| Aligns with `CLAUDE.md` rule "ALL code in .spl" | violates | conforms |
| Cross-platform binary surface | huge          | none beyond winit FFI    |

## 5. Recommendation

**Pick Option B — grow `examples/browser` / `std.gc_async_mut.gpu.browser_engine`
into the V3 shell.** Top three reasons:

1. **The engine already exists and is already wired.** `browser_compositor_
   backend.spl` *already* imports `std.gc_async_mut.gpu.browser_engine.{dom,
   css,layout,paint,widget_to_dom}` and runs the
   `widget→DOM→layout→paint→scene→buffer` pipeline. CEF would force us to
   throw that work away and build a parallel rendering path through Blink.
2. **Charter alignment.** `CLAUDE.md` says "ALL code in `.spl`/`.shs`" and
   the V3 row is titled *"Pure Simple + Chromium host"*. CEF makes V3 "Pure
   C++ rendering with a Simple message bus", which is what V4 (Electron) is
   already for. Two C++-blob variations is one too many.
3. **Leverage compounds.** Every hour spent on `simple_browser` also pays
   down `src/app/ui.web` (HTML dump path), `src/app/ui.tui_web`
   (terminal-rendered DOM), the WPT compat report, and the
   `feature/script/engine/*` JS work. CEF only pays for V3.

Option A's strengths (Blink/V8 maturity, WebGPU, sandboxing) are real but
they buy capabilities V3 doesn't need to ship — and they block on a
cross-platform CEF release-engineering effort the project hasn't started.

## 6. Gating milestones for Option B before V3 can start

V3 is "the same `DesktopShell` apps run inside a windowed simple_browser and
hit the `wm_compare` golden gate". Below are the milestones that must be
green before opening V3 work, with a one-line gate per milestone. Each
milestone is small enough to be a single tracking ticket.

| # | Milestone | Gate |
|---|-----------|------|
| M1 | `ui.chromium/main.spl` skeleton: own a winit window, drive the existing `browser_compositor_backend` into its pixel buffer, present via `rt_winit_buffer_create`/`present_rgba`. | `bin/simple run examples/simple_os/desktop_shell --backend chromium` opens a window showing the existing taskbar. No interactivity required. |
| M2 | Input bridge: translate winit keyboard/mouse events into the DOM event types in `examples/browser/entity/dom/event_types.spl` and into `common.ui.event`. | `test/sys/wm_compare/input_event_chromium_spec.spl` passes the same input cases as the PS/2 and hosted backends. |
| M3 | CSS coverage gap closure for the widgets `DesktopShell` actually paints: finish the subset of `display`, `border`, `background`, `flex`, `grid`, color functions used by the dark/light theme constants in `browser_compositor_backend.spl`. | `examples/browser/test/compat/external/wpt_compatibility_report.md` shows ≥80% on the categories the shell exercises (the rest can stay red). |
| M4 | Widget→DOM→paint→scene round-trip via the *engine in `examples/browser/`* (not only the duplicate at `src/lib/.../browser_engine/`). Decide whether to merge the two engines or keep one as the canonical V3 engine. | A single `use` graph; no duplicated layout/paint code between `examples/browser/feature/layout/*` and `src/lib/gc_async_mut/gpu/browser_engine/layout/*`. (Recommendation: keep `std.gc_async_mut.gpu.browser_engine` as the canonical one; demote `examples/browser` to feature labs and tests.) |
| M5 | `wm_compare` parity: same `DesktopShell` rendered through V1 (baremetal fb), V2 (winit), V3 (simple_browser shell) — ≤1% perceptual diff. | `test/sys/wm_compare/v1_v2_v3_parity_spec.spl` green. This is the V3 acceptance artifact. |
| M6 | Stretch (post-V3): JS event loop wired so `web_api/timer_binding` and `event_binding` can drive a Simple-authored DOM app in the shell. | `examples/browser/smoke_test.spl` runs end-to-end inside the shell window. |

M1–M5 are the V3 critical path. M6 is the line beyond which "simple_browser"
starts being a usable end-user browser — explicitly out of scope for the V3
plan unblock.

## 7. Open questions / unknowns this doc does not resolve

- **Two engines.** `examples/browser/feature/...` and
  `src/lib/gc_async_mut/gpu/browser_engine/...` overlap. M4 forces a merge
  decision; this doc recommends keeping the `std.` one and folding
  `examples/browser` into tests + feature labs, but does not commit to it.
- **JS engine completeness.** `examples/browser/feature/script/engine/jit.spl`
  exists but its maturity isn't visible from file listings alone. V3 itself
  doesn't need JIT, so this is a non-blocker, but flagging it.
- **WebGPU.** `gui_drawing_layer_variations.md` lists the WebGPU path in
  `engine2d` as a separate gap. This doc treats that as orthogonal — V3 ships
  on the software path first.
- **No README in `examples/browser`.** There is no top-level README and no
  written milestone list in the directory; the only doc is the WPT report.
  The "12-milestone in-repo browser" referenced in user memory
  `project_browser_platform` is **not** discoverable from the tree itself.
  M1–M5 above are derived from V3 needs, not from a pre-existing milestone
  list inside `examples/browser/`.

## 8. References

- `doc/03_plan/gui_drawing_layer_variations.md` — V3 definition (§2 "V3"), open
  decisions (§5), work plan item 5 (§4).
- `doc/04_architecture/cross_platform_wm.md` — winit FFI surface that the
  V3 shell will reuse.
- `src/os/compositor/browser_compositor_backend.spl` — already imports
  `std.gc_async_mut.gpu.browser_engine.*`; this is the integration point.
- `src/os/compositor/browser_backend.spl` — sibling render backend.
- `src/app/ui.browser/`, `src/app/ui.web/`, `src/app/ui.electron/` — existing
  app-side adapters; `src/app/ui.chromium/` does not exist yet (this is
  plan item 5's artifact).
- `examples/browser/` — 62,760 LOC across `entity/`, `feature/`, `transform/`,
  `shared/`, `test/`, plus top-level `mod.spl`, `render_adapter.spl:514`,
  `ui_bridge.spl:450`, `devtools_panel.spl:378`, `smoke_test.spl`.
- `examples/browser/test/compat/external/wpt_compatibility_report.md` —
  current WPT baseline (2026-04-08).
- `src/lib/gc_async_mut/gpu/browser_engine/` — ~5,993 LOC, the engine the
  compositor backend already calls.
- `.claude/memory/ref_sffi.md` — SFFI surface that *would* host CEF bindings
  if Option A were chosen.
- `CLAUDE.md` — "ALL code in `.spl`/`.shs`" rule.
- User memory `project_browser_platform` (referenced by the plan) — describes
  a 12-milestone in-repo browser; not mirrored in tree as a checklist file.
