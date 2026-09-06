# tools/composite_diff — Chrome ↔ Simple compositing-stage differential

Stage 6 of the per-component Chrome↔Simple renderer differential — one level
below `tools/paint_diff`: compare the **layerization decision** each engine
makes for the same HTML fixture, not the paint ops within a layer.

* Chrome's output: `LayerTree.layerTreeDidChange` (layer structure) +
  `LayerTree.compositingReasons` (why each layer was promoted).
* Simple's output: `simple_web_layout_render_html_draw_ir` →
  `DrawIrComposition.batches` — Simple's only unit of independently-submitted
  backend work, the closest existing counterpart to a composited layer.

This is an **input/output** comparison per rendering component, not a
whole-page pixel comparison. See `CONTRACT.md` for the canonical model, the
scaffolding-layer classifier, and why compositing (not raster/tiling) was
chosen as the next stage.

## Run

```sh
sh tools/composite_diff/run_composite_diff.shs
# or point at a specific browser
sh tools/composite_diff/run_composite_diff.shs --chrome /path/to/chrome
```

Outputs (all gitignored):

```
out/chrome/<fixture>.chrome.json    layer list + compositing reasons per fixture
out/simple/<fixture>.simple.json    DrawIrComposition batches, trigger-property slice
out/composite_report.json           findings, with BOTH engines' values
out/summary.txt                     flat key=value gate for the system spec
```

Exit codes: `0` compared successfully (findings are data, not failure),
`2` nothing was compared or Chrome promoted 0 elements (vacuous fixture set),
`4` no chrome executable found.

## Fail-closed design

Same two silent CDP failure modes as `tools/paint_diff` (`--disable-gpu`,
premature `LayerTree.enable`), plus one specific to this stage: a fixture
where Chrome promoted zero elements reads exactly like "perfect agreement." So:

* the Chrome extractor exits non-zero if the run-wide element-promotion total
  is 0, or if any single fixture shows zero scaffolding layers (classifier
  broke);
* a fixture with 0 layers/units on either side is reported **BLOCKED**, never
  PASS;
* the summary always prints layer/unit counts compared on *each* side, plus
  `distinct_compositing_reasons` so a degenerate fixture set (testing only one
  trigger) is visible even on a "clean" run;
* every finding states **both** Chrome's value and Simple's value.

## What this stage found

**Simple has no layerization pass at all.** `src/lib/cc/entity/layer.spl`
defines `Layer`/`LayerTreeHost`, but nothing in the browser engine ever
constructs one. `DrawIrComposition` always has exactly one batch
(`html-layout-0`) regardless of `will-change`, `transform`, `position: fixed`,
animations, `preserve-3d`, or any other Chrome compositing trigger. This is a
`src/lib` gap and, per this task's scope (`tools/**`/`test/**`/`doc/**` only),
is **reported, not fixed**.

## Measured baseline (Chrome for Testing 151.0.7922.34, 800×600)

18 fixtures, **95 Chrome layers (23 element promotions)** vs **19 Simple
compositing units (88 components)**, **60 divergences**, spanning **10**
distinct Chrome compositing reasons (`WillChangeTransform`,
`WillChangeOpacity`, `3DTransform`, `Transform3DSceneLeaf`,
`Preserve3DWith3DDescendants`, `BackfaceVisibilityHidden`,
`ActiveOpacityAnimation`, `ActiveTransformAnimation`, `OverflowScrolling`,
`Overlap`). 2 fixtures match exactly: `01_no_promotion`, `14_z_index_only` —
both negative controls where Chrome promotes nothing.

| category | count | example (chrome value / simple value) |
|---|---|---|
| `promotion-missing` | 19 | every Chrome element promotion has no independent Simple unit — see "What this stage found" |
| `no-layerization` | 15 | whole-fixture: Chrome split into layers, Simple emitted one batch |
| `trigger-property-inert` | 10 | `02_will_change_transform`: chrome=`WillChangeTransform (driven by CSS will-change)` / simple=`` `will-change` = "transform" present in Draw IR, no layerization consumes it `` |
| `trigger-property-absent` | 8 | `05_rotate_3d`: chrome=`3DTransform (driven by CSS transform)` / simple=`` `transform` absent; component carries 9 trigger prop(s): backdrop-filter, position, transition-property, animation-name, transform-origin, transform-box, transform-style, z-index, will-change `` (note: `transform` itself is not one of the 9 — the property that actually drives promotion never reaches the Draw IR, only its siblings do) |
| `layer-transform-absent` | 3 | `05_rotate_3d`: chrome=`layer transform matrix with 3D component: [0.906,0,-0.423,0,...]` / simple=`no transform on command "div_3"; transform absent from computed style` |
| `promoted-box-absent` | 4 | `07_position_sticky`: chrome=`layer 32 800x1240 draws=true [Overlap]` / simple=`no component with size 800x1240 in 8 component(s)` — the scroll content's own overlap-promoted layer has no Simple-side counterpart box at all |
| `unit-count` | 1 | `15_static_opacity` (a negative control on the CHROME side — `opacity: 0.5` alone does not trigger Chrome promotion): chrome=`0 element layer(s) above the root scaffolding` / simple=`1 batch(es) above the first` — Simple emits **2** Draw IR batches here even though Chrome stayed at one layer; the opposite-direction defect from every other finding in this stage |

**Structural headline:** `05_rotate_3d` shows the sharpest form of the gap.
Chrome names the promotion reason as `transform` (`3DTransform`) and records a
full 3D transform matrix on the layer. Simple's Draw IR carries 9 *other*
compositing-adjacent style properties on the same component (`position`,
`z-index`, `will-change`, `transform-origin`, `transform-style`, ...) but not
`transform` itself — the one property that actually matters here never
reaches the Draw IR at all, while its neighbours do. That is a style-plumbing
gap, separate from and upstream of the layerization gap.

`unit-count` on `15_static_opacity` is the one finding in this baseline that
does NOT reduce to "Simple should have made more units." Static opacity alone
does not promote in Chrome, yet Simple's Draw IR still forked into 2 batches —
worth investigating on its own, independent of the missing-layerization defect
that dominates the other 59 findings.

All 60 findings trace to two `src/lib` gaps (no layerization pass constructing
`Layer`/`LayerTreeHost`, and `transform`/`position`/`opacity`/`overflow-x/y`
missing from the paint-stage style forwarding list); per this task's scope
(`tools/**`/`test/**`/`doc/**` only) they are **reported, not fixed, here**.


## Files

| file | role |
|---|---|
| `chrome_composite_dump.js` | CDP extractor; layer list + compositing reasons → canonical model, strips scaffolding |
| `simple_composite_dump.spl` | runs Simple's paint pipeline, emits DrawIR batches + trigger-property slice as JSON |
| `composite_diff.js` | lifts both sides, matches promoted layers to components by size, writes the report |
| `run_composite_diff.shs` | driver |
| `fixtures/*.html` | 18 fixtures, each isolating one compositing trigger (incl. 2 negative controls) |
| `CONTRACT.md` | the stage I/O contract |

Sibling stages: `tools/web_diff` (DOM + cascade), `tools/layout_diff`
(layout + text), `tools/paint_diff` (paint ops within a layer). Spec:
`test/03_system/browser_engine/chrome_composite_differential_spec.spl`.
