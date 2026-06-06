# Plan — Draw.io-compatible SDN Draw IR

**Date:** 2026-06-06
**Feature:** `draw_io_sdn_draw_ir`
**Research:** `doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md`
**Status:** Proposed
**Owners:** `src/lib/common/ui`, `src/app/ui.test_api`,
`src/lib/gc_async_mut/gpu/browser_engine`

## Goal

Extend the existing typed Draw IR v1 (`src/lib/common/ui/draw_ir.spl`) into a
shared, debuggable inspection IR that is HTML/CSS box-tree first and Draw.io
(`mxGraph`) compatible second, with tab-indented SDN as the canonical
interchange text, and a gated Protocol-v2 test surface — without breaking the
v1 shared UI contract or forking a second model.

## Guardrails (non-negotiable)

- **No second model.** All growth is additive on `DrawIr*`. Bump `schema` to
  `simple-draw-ir-v2` when the wire shape grows; v1 producers must still
  validate (new fields default-empty).
- **v1 contract is frozen.** Layout / CSS / absolute-position / pixel
  assertions ship as **Protocol v2 / optional Draw-IR extension** behind a
  capability flag and a bumped `X-UI-Protocol-Version`. Never edit v1
  `/api/test/*` endpoints or the §7 assertion table.
- **Pure Simple, SDN-first.** `.spl` only, `[T]` arrays, `<>` generics, no
  preprocessor; SDN (not JSON/YAML) for interchange. Debug gating via build +
  runtime flags, not `#if`.
- **Zero release overhead.** Capture + SDN/Draw.io stringify are skipped when
  the flag is off; style stays typed in the model and is stringified only at
  export.
- **Test policy.** Migrate only pure-Simple API tests; do not migrate
  native-backend-dependent tests. Never silently skip a failing test.

## Phases

### Phase 1 — Model growth (v2 schema) + specs
- Add to `DrawIrCommand`: new `kind` values (`edge`, `path`, `image`, `group`,
  `port`); optional geometry `border_rect` / `content_rect` / `hit_rect` /
  `clip_rect`; optional `computed_style` key-value list (border-radius, padding,
  display, z-index, …).
- Add `DrawEdge` (`id`, `source`, `target`, `routing` =
  straight|orthogonal|bezier, `points: [Point]`, `style`).
- Bump `DRAW_IR_SCHEMA_VERSION` → `simple-draw-ir-v2`; keep `rect`/`text`
  byte-compatible; default new fields so existing `wm_scene`/`html_ast`/
  `gui_ast` producers continue to validate unchanged.
- **Files:** `src/lib/common/ui/draw_ir.spl`.
- **Spec:** extend `doc/06_spec/01_unit/lib/common/ui/draw_ir_spec.md` +
  `test/01_unit/lib/common/ui/draw_ir_spec.spl` (v1 round-trip still green).
- **Exit:** v1 producers validate under v2 schema; new fields constructible.

### Phase 2 — SDN skin (`draw_ir ↔ sdn`)
- New `src/lib/common/ui/draw_ir_sdn.spl`:
  - `draw_ir_to_sdn(composition) -> text` — tab-indented, grammar
    `draw_ir v1` / `meta` / `cell|box` / `geometry` / `point` (per research doc).
  - `sdn_to_draw_ir(text) -> DrawIrComposition`.
- Hand-rolled emit/parse (no generic reflection encoder exists in repo).
- **Spec:** `test/01_unit/lib/common/ui/draw_ir_sdn_spec.spl` — round-trip
  equality on the WM composition from `window_scene_draw_ir.spl`.
- **Exit:** `compose → to_sdn → sdn_to → compose'` is structurally equal.

### Phase 3 — Draw.io (`mxGraph`) skin
- New `src/lib/common/ui/draw_ir_drawio.spl`:
  - `draw_ir_to_mxgraph` / `mxgraph_to_draw_ir`.
  - Mapping: `mxCell.id↔id`, `parent↔parent`, `vertex=1↔box`, `edge=1↔DrawEdge`,
    `mxGeometry(x,y,w,h)↔geometry`, `style="a=b;c=d;"↔computed_style/style map`.
- Canonical model stays `DrawIrComposition`; mxGraph is import/export only.
- **Spec:** `test/01_unit/lib/common/ui/draw_ir_drawio_spec.spl` — import a
  small fixture, export, re-import; assert node/edge identity preserved.
- **Exit:** lossless round-trip for box + edge + geometry + style on a fixture.

### Phase 4 — Producer enrichment
- WM: emit `hit_rect` / `clip_rect` and z-index style from
  `window_scene_draw_ir.spl`.
- Web: emit computed style + border/content/hit rects into the `html_ast`
  source from `simple_web_html_layout_renderer.spl`.
- **Exit:** SDN dump of a real web page + WM scene shows populated geometry and
  computed style for known IDs.

### Phase 5 — Gated Protocol-v2 inspection endpoint
- `app.ui.test_api`: `/api/test/draw-ir`, `?id=`, `/draw-ir/diff`,
  `/layout?id=`, behind a capability flag; responses carry bumped
  `X-UI-Protocol-Version`.
- Record the extension in `doc/04_architecture/ui/shared_ui_contract.md`
  (new "Protocol v2 / Draw-IR extension" section + support matrix rows).
- **Exit:** endpoint returns SDN/JSON Draw IR for a running web surface; v1
  endpoints unchanged; capability advertised.

### Phase 6 — `expect_draw` matcher (gated)
- Add `expect_draw` over `UITestClient` (`src/lib/nogc_sync_mut/ui_test/`):
  `visible`, `geometry … tolerance N`, `hit_rect contains x y`, `css <prop>
  <val>`, `parent <id>`, `kind`/`role`.
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
  and is the first browser-dependent step. The gated endpoint/matcher (5–6) is
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
