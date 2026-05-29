# ADR-002 — Canonical Browser Engine for V3 simple_browser shell

- **Status:** Accepted
- **Date:** 2026-04-14
- **Owners:** V3 simple_browser shell (Row 5, M4)
- **Context doc:** `doc/03_plan/v3_simple_browser_milestones.md` §§ 1.4, 3, 4

## Context

The Simple Language Compiler repository currently contains **two parallel
browser engine implementations** that each cover some overlap of DOM,
style, layout, paint, and render scene generation:

1. `src/lib/gc_async_mut/gpu/browser_engine/*.spl` (~6 k lines) — the
   compact, production-oriented engine. Imported by
   `src/os/compositor/browser_backend.spl` and
   `src/os/compositor/browser_compositor_backend.spl`, which are the
   render backends the V3 chromium shell already uses.
2. `examples/browser/feature/{dom,style,layout,paint,parser}/...`
   (~45.7 k lines) — the maximalist "Chromium-class browser" research
   tree. Includes a JS engine (`script/engine/jit.spl`), a full display
   list pipeline, and entity/dom node stores under
   `examples/browser/entity/dom/`.

The V3 shell plan (`v3_simple_browser_milestones.md` §4) calls out that
this duplication is non-deterministic for V3: a second engine path means
two distinct DOM types, two distinct style resolvers, and two distinct
paint pipelines can both be reached from the chromium shell binary.

M4 is the milestone that resolves the decision.

## Decision

**The canonical browser engine for the V3 simple_browser shell is
`src/lib/gc_async_mut/gpu/browser_engine/`.**

Every `use` site in the V3 graph — specifically under
`src/os/compositor/` and `src/app/ui.chromium/` — resolves to that path.
`examples/browser/feature/...` is demoted to **research / test fixtures
only** and MUST NOT be imported from `src/lib/` or from the V3 shell
import graph.

## Rationale

- **Smaller surface.** The canonical engine is ~6 k lines vs. ~45.7 k.
  Bootstrap, lint, and test times scale with this.
- **Already load-bearing.** `browser_compositor_backend.spl` — the only
  render backend the chromium shell binary currently links — imports
  from the canonical path. Picking it means zero pixel drift from the
  M3 CSS subset work that already shipped.
- **Scene-first.** The canonical engine exposes
  `layout.layout_to_scene(root, w, h) -> RenderScene`, a single-call
  DOM → layout → paint → scene entry point. The examples tree instead
  exposes a multi-stage `DisplayList` pipeline that would need a
  separate adapter to reach the compositor.
- **No JS dependency.** V3 explicitly does not run JavaScript (see M6
  and M9 in the milestones doc). The examples tree pulls in
  `script/engine/jit.spl` transitively, which is dead weight for V3.
- **Spec parity.** The M3 CSS subset tests
  (`test/unit/app/ui.chromium/css_spec.spl`) are written against
  `std.gc_async_mut.gpu.browser_engine.dom` / `style_block`. Keeping
  that engine canonical means the M3 acceptance does not have to be
  reproved against a different DOM representation.

## Consequences

### Positive

- Single import graph for V3. The chromium shell binary links exactly
  one DOM type, one `StyleProps`, one `BeLayoutBox`.
- `wm_compare` M5 gate measures the canonical engine, so V3 parity is
  enforced end to end.
- Future work (M6 tabs, M7 WebGPU, M10 DevTools) inherits a stable
  canonical target.

### Negative / follow-ups

- The examples tree's JS engine (`examples/browser/feature/script/`)
  is not usable from V3 without a separate bridge. V3 does not need it;
  M9 decides whether to keep or delete it.
- `src/lib/nogc_sync_mut/web_ui/*` still imports from `examples/`. That
  path is **not** part of the V3 chromium shell graph (it is the
  baremetal web UI experiment) and is explicitly out of M4 scope. A
  follow-up ticket will migrate or retire that path.
- The M2 `event_bridge.spl` still imports `examples.browser.entity.dom.
  event_types.{DomEvent}` for its wheel-event translator. That import
  is frozen under M2 per the milestones doc (M2 files must not be
  touched by M4). When M2 is reopened, the `DomEvent` type will be
  moved to the canonical engine or replaced with a local alias; until
  then this is the only documented exception in the V3 graph.

## Acceptance check (M4)

- [x] ADR filed at `doc/04_architecture/adr/ADR-002-canonical-browser-engine.md`.
- [x] Every `use` site under `src/os/compositor/` and
      `src/app/ui.chromium/` (excluding the frozen `event_bridge.spl`)
      resolves to `std.gc_async_mut.gpu.browser_engine.*`.
- [x] `src/app/ui.chromium/engine_merge.spl` exposes the canonical
      DOM → layout → scene → pixel entry point the shell uses, so the
      M5 `wm_compare` gate measures the canonical engine end to end.
- [x] Smoke spec at
      `test/unit/app/ui.chromium/engine_merge_spec.spl` constructs a
      minimal DOM, runs it through the canonical pipeline, and asserts
      a non-empty layout + scene result with `.to_be_true()`.
- [ ] `wm_compare` golden diff ≤1 % (enforced by M5, not M4).
