# Plan — Draw.io-compatible SDN Draw IR

**Date:** 2026-06-06
**Feature:** `draw_io_sdn_draw_ir`
**Research:** `doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md`
- Keep the existing `/api/test/*` v1 endpoints stable. Draw IR inspection is an
  advertised optional extension, not a replacement for element/state/action
  endpoints.
- **Pre-impl spec:** `draw_ir_inspection_contract_spec.spl` fills the endpoint,
  protocol-header, capability-gate, and v1-compatibility cases with real
  assertions; no placeholder false-fail case is used.
- **Exit:** endpoint returns SDN/JSON Draw IR for a running web surface; v1
  endpoints unchanged; capability advertised.

### Phase 6 — `expect_draw` helper (gated)
- Add `expect_draw` over `UITestClient` (`src/lib/nogc_sync_mut/ui_test/`):
  `visible`, `geometry … tolerance N`, `hit_rect contains x y`, `css <prop>
  <val>`, `parent <id>`, `kind`/`role`.
- Keep `expect_draw` as a UI helper used inside normal SPipe specs that import
  `use std.spec`. It must not replace SPipe `expect` or change existing
  `std.spipe` alias compatibility.
- **Pre-impl spec:** `draw_ir_inspection_contract_spec.spl` requires the helper
  to appear in the UI-test layer and checks the geometry / hit-rect / css /
  parent / kind assertion vocabulary from this plan.
- **Exit:** migration samples from the research/proposal pass against a pure
  Simple API test; native-backend tests untouched.

### Phase 7 — Visual diff (later)
- Border / color / text-bounds diff over two compositions by stable ID, reusing
  `doc/01_research/ui/tui/harden_tui_gui_layout_comparison.md` patterns.
- **Exit:** `draw-ir/diff?baseline=` reports per-node geometry/style deltas.

## Sequencing & risk

- Order is smallest-blast-radius first: model + SDN are fully in-Simple and
  browser-free (Phases 1–2), so they are the safe foundation. Draw.io (3) is
  pure text mapping. Producer enrichment (4) touches the large renderer files
  and is the first browser-dependent step. The gated endpoint/helper (5–6) is
  where the contract-version discipline matters most.
- Risk: enriching `simple_web_html_layout_renderer.spl` (115 KB) and
  `window_scene_draw_ir.spl` must stay behind the debug flag so the render hot
  path is unchanged when off (perf-regression guardrail per CLAUDE.md).
- Risk: schema v2 must not break the existing engine2d/web bitmap evidence
  gates; run them after Phase 1 and Phase 4.

## Definition of done

1. `draw_ir.spl` carries v2 model with edges + box geometry + computed style;
   v1 round-trip green.
2. SDN and Draw.io round-trips green on WM + a web fixture.
3. `/api/test/draw-ir*` + `expect_draw` work as a documented, capability-gated
   Protocol v2 extension; v1 contract and tests unchanged.
4. Release builds with the flag off show no new render-path cost.
5. Research, plan, and `shared_ui_contract` v2 section are in sync and pushed.
