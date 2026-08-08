# Pure Simple Web Renderer Chromium Quality Plan

Date: 2026-06-03
Status: Draft

## Goal

Build the pure Simple Web Renderer into a high-fidelity 2D software renderer
that can be compared against Chromium on a deterministic HTML/CSS corpus. The
renderer target is CPU first, with SIMD acceleration for hot pixel paths, and a
graphic comparison harness that separates exact deterministic regressions from
expected browser rasterization differences such as font antialiasing.

This plan extends:

- `doc/03_plan/graphical_backend_equality.md`
- `doc/03_plan/simple_web_renderer_chrome_compat_corpus.md`
- `doc/03_plan/render_2d_optimization_plan_2026-05-30.md`

## Scope

In scope:

- Pure Simple HTML/CSS rendering for the supported offline corpus.
- Deterministic 2D CPU framebuffer rendering.
- SIMD acceleration for fill, copy, blit, alpha blend, scroll, solid borders,
  clips, and common compositing spans.
- Chromium screenshot and metric baselines for supported fixtures.
- Pixel, perceptual, geometry, and text-metric comparison reports.
- CI-friendly artifact production with small focused gates and larger manual
  corpus sweeps.

Out of scope for this phase:

- Full web platform compatibility.
- JavaScript engine parity.
- GPU parity as a release blocker.
- Network-loaded pages as primary evidence.
- Bitwise equality with Chromium text rasterization.

## Quality Contract

The renderer is "Chromium-quality for this phase" only when all supported corpus
features have one of these evidence states:

- Exact match: Simple and Chromium pixels are bitwise identical.
- Perceptual match: pixel differences are inside the approved tolerance profile
  and classified as antialiasing, text rasterization, or subpixel edge deltas.
- Explained divergence: report identifies the unsupported feature, bounding
  box, affected DOM/style region, and linked requirement or bug.

No fixture may pass by using an oracle fixture path that bypasses the production
renderer unless the test name and report explicitly say it is a harness-only
fixture.

## Renderer Architecture Plan

1. HTML parsing
   - Keep the accepted subset explicit in fixture metadata.
   - Reject unsupported constructs with structured diagnostics.
   - Preserve source order, text nodes, attributes, classes, ids, and inline
     style ranges needed by CSS matching.

2. CSS cascade and computed style
   - Implement deterministic selector matching for supported selector forms.
   - Compute inherited and initial values into a stable style record.
   - Store Chromium sidecar metrics for body margin, font, display, box sizing,
     line-height, padding, border, background, overflow, and flex properties.

3. Layout
   - Normalize all layout output into integer or fixed-point layout records.
   - Cover block flow, inline text wrapping, margins, padding, borders,
     overflow clips, simple flex row/column, form-control boxes, and list
     markers.
   - Compare Simple layout records against Chromium DOMRect and text line
     sidecars before using pixels alone.

4. Paint
   - Paint background, border, text, marker, replaced placeholder, and form
     control primitives into explicit display items.
   - Add display-item dumps to every failed comparison.
   - Keep paint order and clip stack deterministic.

5. Raster and compositing
   - Route all software pixels through the shared 2D CPU framebuffer path.
   - Add SIMD kernels only behind the same scalar contract.
   - Keep scalar and SIMD outputs bitwise equal for the Simple renderer.
   - Use Chromium tolerance only across the browser boundary.

## 2D SIMD CPU Plan

Priority operations:

1. `fill_rect`
   - SIMD span fill for aligned middle runs.
   - Scalar prologue/epilogue for unaligned edges.
   - Exact scalar/SIMD equality test for all widths 0..257 and selected large
     widths.

2. `copy_span` and `blit_rect`
   - Forward/backward copy correctness for overlapping source and destination.
   - SIMD middle copy with scalar edge handling.
   - Scroll fixtures that prove no tearing or stale rows.

3. `alpha_blend`
   - Porter-Duff source-over for premultiplied or documented straight-alpha
     representation.
   - SIMD and scalar equality on fixed random seeds.
   - Separate perceptual policy only when comparing to Chromium.

4. `border` and `clip`
   - Fast horizontal and vertical solid border paths.
   - Rectangular clip stack enforced before raster writes.
   - Clip overflow tests that compare exact expected pixels.

5. `text blit`
   - Glyph bitmap placement and clipping.
   - Baseline and line-box diagnostics.
   - Chromium comparison remains tolerant until the font rasterizer is proven
     compatible enough for exact checks.

## Graphic Compare Test Plan

### Fixture Layers

- Unit pixel specs: exact scalar framebuffer expectations.
- Renderer component specs: exact Simple DOM/style/layout/paint records.
- Engine2D software specs: exact scalar versus SIMD framebuffer equality.
- Chromium oracle specs: screenshot and metric comparison for selected pages.
- Corpus sweep: all offline corpus pages with artifact freshness checks.

### Artifact Layout

Use stable per-fixture directories:

```
test/09_baselines/web_renderer/<fixture_id>/chromium.ppm
test/09_baselines/web_renderer/<fixture_id>/chromium_metrics.json
test/09_baselines/web_renderer/<fixture_id>/simple.ppm
test/09_baselines/web_renderer/<fixture_id>/simple_layout.sdn
test/09_baselines/web_renderer/<fixture_id>/simple_paint.sdn
test/09_baselines/web_renderer/<fixture_id>/diff.ppm
test/09_baselines/web_renderer/<fixture_id>/report.sdn
```

Reports must include:

- fixture id, viewport, device scale factor, color space, renderer mode
- capture freshness hash and command line
- exact differing pixel count
- max channel delta and SAD
- perceptual match percentage
- diff bounding boxes
- DOM/text region attribution
- accepted tolerance policy
- status: exact, accepted, divergent, failed_capture, unsupported

### Comparator Policies

- `simple_exact`: scalar versus SIMD and Simple internal baselines; zero
  tolerance.
- `chromium_geometry`: DOMRect, line string, and computed style sidecar checks;
  small numeric tolerances only where Chromium exposes fractional values.
- `chromium_pixel_strict`: exact or near-exact for boxes, backgrounds, padding,
  margins, and solid colors.
- `chromium_pixel_text_tolerant`: antialias-aware tolerance for glyph and edge
  raster differences.
- `unsupported_feature`: fail unless the fixture metadata declares the feature
  unsupported and the report identifies the missing implementation.

## Corpus Expansion Plan

Phase A: Stabilize the current 16 focused fixtures.

- Require production renderer mode for every fixture.
- Remove fixture-oracle fast paths from pass criteria.
- Keep text-tolerant policy only where reports prove layout lines match.

Phase B: Promote the 132 offline famous-site-inspired corpus.

- Generate Chromium baselines with Playwright/CDP.
- Generate Simple production captures with watchdog limits.
- Store Chromium metrics sidecars for every page.
- Fail on stale or missing artifacts.
- Track first divergent fixture per feature class.

Phase C: Add WPT-inspired reftests.

- Import only self-contained cases that map to the supported CSS subset.
- Keep expected rendering local and deterministic.
- Use Chromium as the browser oracle and Simple exact tests as implementation
  gates.

## Implementation Phases

1. Requirements and NFRs
   - Write final requirement docs for renderer quality, graphic comparison, and
     SIMD CPU behavior.
   - User must select feature and NFR options before implementation.

2. Test harness foundation
   - Add stable artifact paths and report schema.
   - Add freshness hashes and command provenance.
   - Add failure classification that cannot silently accept missing captures.

3. Production renderer capture
   - Route corpus fixtures through the real Simple Web Renderer.
   - Add layout and paint dumps for failed captures.
   - Preserve current fixture-oracle tests only as harness diagnostics.

4. Scalar correctness
   - Prove all supported CSS primitives with exact framebuffer tests.
   - Add DOM/style/layout/paint record specs for every primitive.

5. SIMD acceleration
   - Wire native SIMD kernels behind scalar-equivalent APIs.
   - Add scalar/SIMD fuzz-style fixed-seed equality.
   - Add perf reports for 1920x1080 and 320x240 representative frames.

6. Chromium fidelity
   - Enable Chromium baseline generation and metric sidecars for focused
     fixtures.
   - Promote fixtures from tolerant to strict as implementation improves.
   - Keep text differences attributed to line metrics, glyph paint, or
     compositing.

7. Corpus gate
   - Run the full offline corpus with production renderer captures.
   - Store summary counts: exact, accepted, divergent, unsupported,
     failed_capture.
   - Block release on stale artifacts, failed captures, or unexplained
     divergences.

## Verification Start Set

Focused commands:

```
sh scripts/setup/install-spipe-dev-command.shs --check
find doc/06_spec -name '*_spec.spl' | wc -l
SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/03_system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --clean --format json
SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/03_system/wm_compare/famous_site_engine2d_backend_spec.spl --mode=interpreter --clean --format json
bin/simple run src/app/wm_compare/site_corpus_compat.spl --continue-on-fail --production-renderer --skip-simple-watchdog --simple-timeout-ms=60000
node tools/electron-shell/verify_famous_site_corpus_completion.js
```

Performance commands, once SIMD wiring is active:

```
bin/simple run src/app/wm_compare/site_corpus_layout_report.spl --all
bin/simple run test/02_integration/rendering/engine2d_cpu_metal_parity_run.spl
```

Add a dedicated SIMD benchmark command when the native CPU path exposes stable
timing counters.

## Acceptance Criteria

- The focused fixture set renders through production Simple Web Renderer only.
- Scalar and SIMD Simple outputs are bitwise equal for supported operations.
- Chromium comparison reports classify every mismatch with artifact evidence.
- No missing baseline, stale report, or fixture-oracle path can produce a pass.
- Full corpus summary is reproducible from checked-in fixtures or generated
  artifacts.
- Release verification includes `find doc/06_spec -name '*_spec.spl' | wc -l`
  returning `0`.

## Risks

- Font rasterization may prevent exact Chromium pixel equality for text.
- Browser metric sidecars can drift across Chromium versions.
- SIMD mutable array extern wiring is a known blocker for native acceleration.
- Large corpus sweeps can exceed watchdog limits unless split into focused and
  batch lanes.
- Existing dirty worktree state can make GitHub sync unsafe without isolating
  this plan doc from unrelated changes.

## Bounded HTML progress (2026-07-29)

- Plain `hidden` now enters the canonical cascade as a lowest-priority
  `display:none` presentational default. The shared style result suppresses the
  element and subtree in both software paint and Draw IR; later author
  `display` declarations can override it.
- Exact attribute detection excludes `data-hidden`, `hiddenx`, and quoted text.
- `hidden="until-found"` remains unsupported because reveal-until-found needs
  find-in-page lifecycle and `beforematch` behavior; this slice does not claim
  it or full HTML compatibility.

## Ordered HTML/CSS compatibility matrix (2026-07-29)

| Priority | Surface | Current state | Next canonical owner |
|---|---|---|---|
| P0 | HTML tree construction and recovery | partial: common table and implicit-close contexts exist; full WHATWG/WPT parity is unproven | shared HTML tree builder |
| P0 | CSS cascade, inheritance, selectors | partial: specificity and common selectors exist; complete cascade layers/scoping are unproven | shared CSS cascade |
| P0 | inline formatting | partial: text wrapping exists; `<br>` forced-line semantics are this bounded slice; inline-block/bidi parity remain | shared layout |
| P0 | block sizing and overflow | partial; overflow/z-index evidence is owned by the DrawIR lane | shared layout/Draw IR |
| P1 | flex layout | partial row/column/wrap support; full flex sizing parity unproven | shared layout |
| P1 | grid and table layout | fixed direct and row-grouped tables are bounded-supported; grid, auto table layout, rowspan, and border collapse remain unsupported | shared layout |
| P1 | replaced elements, backgrounds, fonts | partial; fixed single-image background is covered, local/multiple layers remain unsupported | canonical resource/layout/paint owners |
| P1 | transitions and animations | supported bounded path; preserve the single canonical animation clock | style/layout/paint invalidation |
| P2 | interactive HTML semantics | partial; details/dialog/forms and complete accessibility semantics remain unproven | DOM/event/accessibility owners |
| Gate | Chromium/WPT equality | not claimed until pinned corpus receipts and production runtime evidence exist | conformance runner |

This matrix orders compatibility work; it is not a full-browser claim. Each
row advances only with semantic/computed-style/Draw IR evidence before pixels.

## Forced inline line-break progress (2026-07-29)

- `<br>` is assigned its HTML inline default and canonical inline-flow layout
  forces one line-height advance with zero width.
- The system oracle requires ordered text/break/text Draw IR, exact 20 px
  geometry, then software pixel divergence from a single-line control.
- `inline-block`, bidi line breaking, grid, table formatting, and full WPT
  parity remain explicitly outside this bounded slice.

## Fixed CSS background progress (2026-07-29)

- Resolved single-image `background-attachment: fixed` now uses the viewport as
  its positioning area while retaining the element background clip in the
  canonical web semantic/layout to Draw IR lowering.
- The system oracle covers absolute Draw IR geometry, fixed-versus-scroll
  repeat phase, stable viewport tile origin while document scroll moves the
  element shape, the no-repeat edge outside the viewport-anchored tile, and
  Engine2D software readback.
- `background-attachment: local` remains unsupported because canonical layout
  does not yet carry an element scrollport offset; the unsupported ledger now
  names only that remaining behavior.

## GitHub Sync Plan

Do not sync this document together with unrelated worktree changes. The current
safe sync sequence is:

1. Confirm only intended files are included.
2. Run verification for this documentation-only change.
3. Commit the plan doc in its own jj change.
4. Run `jj git fetch`.
5. Rebase the plan-doc change onto `main@origin`.
6. Set the `main` bookmark to the rebased change.
7. Push only after the user confirms the remote SSH issue is fixed.

The existing graphical equality plan records a prior sync failure:
`git@github.com: Permission denied (publickey)`. Treat that as unresolved until
`jj git fetch` and a non-mutating remote check succeed.

## IR and GPU-offload alignment (2026-07-31)

This plan's CPU renderer remains the authoritative correctness oracle. Two new
documents change what sits around it, additively:

- `doc/04_architecture/compiler/mdsoc/mdsoc_plus_tagged_structural_compute_architecture.md`
  — canonical SoA DOM/CSS arenas, CSS selectors compiled to QueryIR, DOM/CSSOM
  mutation as MutationIR transactions, and exact selector-feature invalidation
  (`DirtyMask` + `StyleDifference`) replacing the broad "DOM changed → rerun
  parse/style/layout/paint" behavior. Incremental results must equal this plan's
  full-recompute path for the same snapshot.
- `doc/03_plan/ui/gpu_web_scene_offload_mdsoc_plus_plan.md` — experimental
  GPU-resident WebScene lane and the packed, no-reallocation **DrawIR v3**
  (typed tables, no strings in render-hot structures). DrawIR v2 and this
  renderer are unchanged; v2/v3 compatibility adapters and semantic checksums
  are owned by that plan's Program 2.

Consequences for this plan:

1. New corpus fixtures should also record DrawIR v3 semantic checksums once the
   v3 contract lands, so the Chromium-parity corpus doubles as the GPU-lane
   parity corpus.
2. The comparison harness gains a shadow mode: CPU render authoritative, GPU
   WebScene compared by receipt/IR/pixel — never the reverse until that plan's
   promotion gates pass.
3. Style/layout invalidation work in this plan should target the
   selector-feature model rather than extending the current whole-pipeline
   dirty flag; full recomputation stays as the test oracle.

Per-lane parallel plans: `doc/03_plan/platform/structural_compute/`.
