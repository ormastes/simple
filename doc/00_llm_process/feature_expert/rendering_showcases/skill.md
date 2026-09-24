# Feature Expert — Rendering showcases

## Role

Own the canonical rendering-showcase subtree `examples/06_io/ui/rendering/`
(ten entries + shared item list + UI-base switch), the shared cores under
`examples/ui/rendering_{2d,web}_{core,extended}/`, and the TUI ScreenHost
(`src/app/ui_showcase/hosts/host_tui.spl`). Keep the ten-entry census, the
tier-split contract, and the wiki/guide pointers truthful.

## Invariants

- Ten canonical entries, fixed layout: `rendering_{tui,gui,wm}_{core,full}.spl`,
  `rendering_{2d,web}_{core,extended}.spl`, plus `rendering_items.ui.sdn`,
  `rendering_switch.spl`, `doc.md`. Every entry header declares
  `# lane: <lane>` / `# tier: <tier>` / `# core: <module>`.
- Tier split is file-based: extended/full entries import the core module;
  a `SHOWCASE_TIER`-style env switch is forbidden (kills the NFR-001 loading
  win).
- Honest-fail only: `showcase status=blocked <reason>` /
  `showcase status=pass <path>`; degraded backends, missing fixtures, and
  unrendered items are reported, never silently skipped. The 13 WidgetKinds
  without a TUI renderer are labeled `(no tui)` (43 enum variants, 30
  TUI-rendered — census verified 2026-09-24; do not regress to the old
  44/25/19 estimate).
- Sharing architecture: host-agnostic core + `ScreenHost` trait seam for
  interactive showcases; `.ui.sdn` data for the shared item list. Simple has
  NO parameterized imports — do not add `use m.{k=v}` syntax proposals to
  showcase code.
- WM lane is WM-as-server (HostCompositor + bridge admission +
  `taskbar_model()`), NOT a ScreenHost client; GUI full demonstrates internal
  windows (`simple_gui_internal_window`, titled + borderless).

## Entry points

- Requirements: `doc/02_requirements/feature/rendering_showcases.md` (REQ-001..011);
  NFRs: `doc/02_requirements/nfr/rendering_showcases.md`.
- Design: `doc/05_design/rendering_showcases.md`; architecture:
  `doc/04_architecture/rendering_showcases.md`.
- Spec: `test/03_system/ui_showcase/rendering_showcases_spec.spl`; runtime
  gates: `scripts/check/check-rendering-showcase-closure.shs`,
  `scripts/check/check-rendering-showcase-captures.shs`.
- Run table: `examples/06_io/ui/rendering/doc.md`; guide:
  `doc/07_guide/ui/showcase_apps.md`; wiki: `doc/00_llm_process/llm_wiki.md`
  ("Rendering showcases").

## Known state (2026-09-24)

All ten entries + cores + item list + switch implemented by six parallel
lanes; structural spec 8/8 PASS. Runtime evidence: 2D core/extended PASS
(PPM byte-exact, drag/click gates green), TUI brief/full PASS (capture +
coverage `rendered=30 no_tui=13`), WM brief/full PASS (sabotage + checksum
gates), GUI brief/full PASS (internal-window desktop capture), Web core/
extended PASS under seed (5 tabs, 10 themes, fixture PNG). Blocked:
web-server GUI serving — `bin/simple ui web` exits before bind
(`doc/08_tracking/bug/ui_web_seed_exits_before_bind_2026-09-24.md`); the
UI-base switch `web` branch honest-fails until redeploy. `bin/simple check`
is broken tree-wide
(`doc/08_tracking/bug/check_worker_broken_seed_semantic_2026-09-24.md`) —
verify with `SIMPLE_LIB=src SIMPLE_TIMEOUT_SECONDS=0 bin/simple run`.
Backend selection: `SIMPLE_2D_BACKEND=cpu|cpu_simd|vulkan|metal`, default
vulkan on 2d/web lanes (exact admission, honest-fail on unavailable);
advisory on gui/wm headless captures (CPU raster / compositor pixel buffer).

## Related experts

`../ui_slim_kernel_plugin/skill.md` (composition kernel + feature packs),
`../tiny_ui_web_wm/skill.md`, `../ui_gui/skill.md`.
