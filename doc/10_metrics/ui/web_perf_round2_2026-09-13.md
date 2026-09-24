# Web renderer cold-pipeline perf, round 2 — macOS, 2026-09-13

Interpreter `/Users/ormastes/simple/build/cargo-r2/release/simple`
(`stat -f '%z %m'` = `39528776 1789199850`), `SIMPLE_EXECUTION_MODE=interpreter`,
viewport 900x760, one render per page, all eight catalog pages in ONE process.

Instrument: `build/perfbench/pipeline_bench.spl` (uncommitted lane tool —
`build/` is gitignored). It renders each `examples/06_io/ui/web_catalog/<page>.html`
through `simple_web_layout_render_html_draw_ir_result`, times parse+style+layout+
compose (NOT rasterisation), and prints the full `draw_ir_to_sdn(composition)` so
the display list can be sha256'd outside the process.

**Oracle.** The per-page digest below is `sha256` (first 16 hex) of the complete
Draw IR SDN — every command, rect, colour, text value, advance array and glyph
run. That is a stronger oracle than the raster `frame_digest`
(`src/app/ui/chrome_showcase/gpu_boundary_audit.spl:417`, FNV-1a/32 over pixels),
which is produced only by the boundary audit and costs ~11 min per page per side
on this host; the audit was therefore run once, after the change, for its PASS
verdict rather than as a before/after pixel diff.

## What landed

**Root cause — `src/lib/common/encoding/font_registry.spl:731`
`selected_font_coverage_matrix()`.** The function builds the complete
language-major 10x10 sparse coverage matrix: 100 cells, each running
`_font_coverage_resolution` (`:715`), which itself calls
`selected_font_simple_tuple_accepted` (`:687`) and `_font_direct_category_face`
(`:700`). It was rebuilt from scratch on **every** call of
`selected_font_coverage_cell` (`:752`), which then linearly scans it — and that
is called once per `#text` node from
`selected_font_asset_for_language_category` (`:758`) inside
`_resolve_font_metrics_with_language_config_uncached`
(`src/lib/nogc_sync_mut/text_layout/font_renderer.spl:3193`).

The matrix is a pure function of two static axis lists and static string policy —
no I/O, no registry state — so it is a compile-time constant. It is now memoized
in a module-level `var`, the same shape and the same persistence proof as the
`_selected_font_asset_candidates_cache` memo already sitting 430 lines above it
in the same file.

### Measured, css-layout, `SIMPLE_WEB_PHASE_TRACE=1 SIMPLE_WEB_STYLE_COUNTERS=1`

Sub-attribution of the `cls_ms` bucket was added temporarily (7 timers inside the
classification block) and removed before landing:

| sub-bucket | ms | what |
|---|---|---|
| `cls_sel` — `selected_font_asset_for_language_category` | **431** | the matrix rebuild |
| `cls_cps` — `text_codepoints(content)` | 42 | |
| `cls_cx` — `_resolved_font_complex_script` | 22 | |
| `cls_cat`, `cls_lang`, `cls_cache`, `cls_ident` | 3 / 2 / 2 / 2 | |
| **`cls_ms` total** | **509** | 146 uncached resolves |

After the memo, same instrument, same page: **`cls_ms` 509 -> 160 ms (-3.2x)**.
`cls_sel` collapses to the 146 linear scans of a matrix that is now built once.

### Per-page cold pipeline (ms)

| page | before | after | digest before -> after |
|---|---|---|---|
| `overview` | 748 | 643 | `24ff9a01a5835c04` -> same |
| `html` | 5138 | 4458 | `4e7653123fd99863` -> same |
| `css-layout` | 6383 | 5336 | `7ccee9e87efb7008` -> same |
| `css-paint` | 7544 | 6754 | `aac80a6995c19519` -> same |
| `forms-media` | 1531 | 1296 | `045953f38bdcf9d2` -> same |
| `animation` | 1448 | 1117 | `3e73858ba1e7846f` -> same |
| `evidence` | 194 | 171 | `5e447b7ba7a9dc1b` -> same |
| `tab-bar` | 396 | 315 | `ab87ddd827e3e7fd` -> same |
| **total** | **23,382** | **20,090** | **8 of 8 identical** |

**Honest caveat on the wall-clock column.** This host ran at load 8.5-13.5
throughout; repeat runs of the *same* tree moved `css-paint` between 6,754 and
9,338 ms. A ~350 ms saving on a 6 s page is inside that noise band, so the table
is one paired run and is NOT the evidence. The evidence is the `cls_ms` timer,
which is a direct timer on the changed block and is stable, plus the structural
argument (a 100-cell policy evaluation per text node is now one).

## Targets from the round-2 brief that did NOT land, and why

1. **`sec_inherit_ms` (~0.8-1.2 s css-layout): measured, not fixed.** The brief
   proposed replacing the whole-`Style` copy with an inherited-props record.
   Sub-measurement first: the loop
   (`simple_web_html_layout_renderer_core.spl:2939-2952`) is
   `renderer_default_style()` (a 176-argument constructor literal,
   `..._style.spl:610`) followed by `inherit_from` (~110 `self.X = p.X`,
   `..._style.spl:235-517`). The dead `inherit_style_legacy` (`..._style.spl:620`)
   already expresses the "one constructor instead of default+110 assignments"
   idea, so it was swapped in as a timing probe: **`sec_inherit_ms` 813 -> 794 ms,
   i.e. nothing.** The cost is the single big constructor, which both paths pay,
   not the assignment pass. A real fix therefore needs the architectural change
   (stop materialising a full `Style` per node), which touches every `Style`
   reader and is not landable in one round. Probe reverted; no change shipped.
2. **Per-(font,size,weight) advance cache in `font_advance_layout.spl`: already
   exists, upstream.** `measure_text_advances`
   (`font_renderer.spl:2029`) already resolves an ASCII slot once per run and
   reads `_adv_cache_lookup_slot` per codepoint: measured `adv_hits=4396
   adv_misses=186` — 96% hit. `font_advance_layout.spl` itself is pure batch
   arithmetic with nothing to cache. A second cache would be duplicate state.
3. **Run-level memo shows `run_hits=0`: investigated, NOT a bug.** A temporary
   store counter proved the memo is written (`run_stores=146`, `run_keys=146` for
   146 calls) and that the 146 `(face, size, text)` runs on `css-layout` are
   simply all distinct. Same reason `id_hits=0 id_misses=292` on the
   full-content-keyed identity cache. Counters reverted.
4. **Parse (~1 s): not touched.** `_css_scan_rules_simple`
   (`..._core.spl:659-793`) is already span/`split`-based, not char-by-char
   concat — it was deliberately rewritten that way (see its comment at `:642`).
   Two real O(N^2) shapes remain unmeasured and open: the array rebuild at
   `..._core.spl:1063-1066` and `Style.inherited_digest()`
   (`..._style.spl:519-585`), a ~70-line string built by repeated concat per
   node, which sits *outside* every `sec_*` bucket and so is currently
   unattributed. Next round should time the `style_end - style_start` gap against
   the sum of the `sec_*` counters and start there.
5. **Steady-frame re-upload check (`SIMPLE_VK_ORDER_TRACE=1`): not run.** This
   change is confined to the cold style path and touches no GPU code; the
   boundary audit was run instead as the standing gate.

## Gates

- Draw IR digests: 8 of 8 byte-identical (table above).
- `SIMPLE_BIN=build/cargo-r2/release/simple sh
  scripts/check/check-web-vulkan-gpu-boundary-audit.shs` ->
  `PASS — 2 frame(s) audited, host_pixel_iterations=0, readbacks_per_frame<=1,
  submits_per_frame<=1` (exit 0), with `full_readbacks=0 host_paint_pixels=0
  presenter_readbacks_upload=0 host_fallback_reasons=none`. Without `SIMPLE_BIN`
  the script answers `ERROR — nothing was checked (no runnable Simple
  interpreter)` on this host — fail-closed, not a pass.
- Neighbouring specs, run before and after with identical verdicts (both
  pre-existing failures, unrelated to this change — a pinned manifest sha):
  - `test/01_unit/lib/common/encoding/font_asset_manifest_spec.spl` — 9 examples,
    2 failures, both sides.
  - `test/03_system/app/simple_2d/feature/shared_font_manifest_spec.spl` —
    7 examples, 4 failures, both sides.
