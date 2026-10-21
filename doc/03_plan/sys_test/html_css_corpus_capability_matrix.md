# HTML/CSS corpus capability matrix and admission plan

Status: planning inventory, 2026-09-26. All 48 manifest rows retain `vulkan_parity_status: not-run` and `simple_render_status: not-run`. This document grants no physical Vulkan PASS.

## Common admission contract

Each row starts from its pinned HTML bytes at 640 × 480, DPR 1. Preserve the real Web producer's DOM node and computed-style identity, source command index, geometry, clip/layer order, and `render_degraded` reason through `DrawIrComposition -> draw_ir_to_ui_ir -> UiIr`. Reject a scene before either backend submits when any required semantic is absent. Retain the original source DrawIR digest and the admitted GPU DrawIR digest. Source-only, CPU, offline receipt, and two-backend agreement cannot establish a physical result: both isolated owners must complete and read back the same canonical RGBA domain on the same authenticated physical device/driver UUID, then compare with an independent oracle.

Comparator codes below are **policies to finish before admission**, not tolerance approvals: **X** = exact RGBA against a separately constructed analytic oracle; **R** = pinned independent HTML reference plus an independently derived pixel oracle, exact for integer opaque geometry unless a predeclared edge rule requires a bound; **M** = case 16's manifest candidate (`max_channel_difference=1`, `max_different_pixels=26400`), which still needs an independently justified oracle and bound; **A** = independent geometry/color oracle with a fixture-specific, predeclared antialias/sampling channel and pixel budget; **F** = independent effect/color oracle and predeclared filter bounds, including edge regions; **T** = pin font files, face coverage, shaping/glyph positions and an independent text oracle before a raster bound; **S** = pin requested scroll/animation state and independently derive its expected geometry/pixels before any numeric bound. A pinned Chromium differential is diagnostic, never specification proof. No threshold may be chosen from observed backend mismatches.

The source column names the semantic or external input that must survive the common contract. `checker` means the manifest-pinned `assets/checker.svg` **and** its 80 × 80 decoded RGBA derivative need matching source/derivative digests. `reference` means the separately pinned HTML page; it is neither a screenshot nor a renderer-produced golden. Unless stated, no external asset is present. Every gate also requires full-scene dual-backend preflight, complete physical readbacks, and the row's comparator; the table calls out the additional current blocker.

## Shared implementation stages

1. **Source and evidence spine:** enforce the common contract, complete source-command inventory, asset/font/state receipts, owner-bound completion and UUID identity. Case 01 and 06 have bounded candidate adapters and independent exact oracles, but their actual producer inventories and physical captures remain unverified.
2. **Opaque layout and generated boxes:** reuse rectangular fill/clip for flex/grid placement, translation and pseudo-elements. Validate computed layout, not reference rectangles substituted for source output. Extend the Web admission path by semantic operation family instead of one hardcoded case at a time.
3. **Geometry and paint:** retain f64 geometry, affine order/origin, rounded/elliptical borders, paths/strokes, gradients, images and clipping in versioned shared/native payloads. Case 02 specifically needs fractional CSS dimensions **and** seven-degree rotation; a fractional rectangle implementation alone cannot admit it.
4. **Text and assets:** pin fonts and coverage, shape and place multilingual/vertical/emoji runs, decode checker input with verified derivative, then implement sampling/object-fit and SVG commands. A page background cannot stand in for missing text/image/SVG commands.
5. **Layers and effects:** add balanced opacity/isolation groups, blend modes, shadows, filters, masks, backdrop-root sampling and 3D/animation state with explicit bounds and completion. Compound sites 44, 46 and 47 qualify only after every constituent operation is preserved; 45 and 48 additionally depend on the text/font stage.
6. **Physical matrix:** freeze each row's oracle/tolerance **before** execution; run admitted Engine2D and upstream Skia Vulkan owners on Linux; bind binary/revision, source/asset digests, UUIDs, completion, canonical pixels and retained capture to a fresh run. Keep unsupported rows blocked rather than accepting approximations.

## Per-case gates

| Case | Required operation family | Source/state/asset to preserve | Comparator | Current additional gate |
| --- | --- | --- | --- | --- |
| 01 solid boxes | opaque rect, full-scene clip/order | Three authored divs and `#scene`; reference | X | Candidate adapter/oracle only; observe expected seven producer commands and run real dual capture. |
| 02 fractional edges | f64 rect, affine rotation, coverage | Decimal left/top/width; authored `translate(.25px,.25px) rotate(7deg)` with matrix `T × R` about resolved origin | A | Web integer fields and quarter-turn transform path lose semantics; define AA rule after f64/affine preservation. |
| 03 elliptical corners | unequal elliptical rrect, AA | Four horizontal/vertical radius pairs | A | Strict bridge rejects nonzero radius; add typed per-corner geometry and both raster paths. |
| 04 radius normalization | normalized elliptical border/rrect | Oversized radii and 12px border | A | Resolve CSS radius scaling and inner/outer border coverage without approximation. |
| 05 border styles | per-side stroke pattern, rounded border | Solid/dashed/double/dotted sides; second rounded box | A | Preserve four distinct side styles, joins and dash phase. |
| 06 rectangular clip | parent overflow clip, opaque rect | Actual child geometry and parent clip; reference | X | Candidate adapter/oracle only; observe source clip inventory and run real dual capture. |
| 07 integer transform | translated opaque rect | `translate(150px,80px)` and original position; reference | R | Promote source-derived translation through shared IR; build/check oracle and physical captures. |
| 08 transform order | affine composition, origin, AA | Rotate/translate/scale order differs between boxes | A | Six-coefficient transform, origin and clip space need typed round-trip on both paths. |
| 09 linear gradient | angled stops and alpha | Hard 25% stop, transparent end | A | Add gradient stop interpolation/color-space contract and GPU parity. |
| 10 radial gradient | elliptical focal gradient | Center at 35% 65%, four stops | A | Add resolved radial geometry and edge sampling parity. |
| 11 conic gradient | angular gradient, circular clip | `from 35deg`, repeated red seam, 50% radius | A | Conic seam/interpolation and circle coverage need explicit operations. |
| 12 repeating gradient | periodic gradient | 12/24px stop cycle at 45deg | A | Preserve repeat period and phase rather than flattening to one ramp. |
| 13 background layers | radial overlay, tiled image, rrect | Layer order/size/position/repeat; checker | A | Verify decoded checker and layer compositing; current rectangle provider rejects image/gradient. |
| 14 multiple shadows | ordered outset shadows, blur/spread | Three different shadow layers and rounded box | F | Preserve layer order, spread, blur kernel and effect bounds. |
| 15 inset shadows | inset blur/spread, rrect | Two inset shadows and asymmetric radius | F | Add interior clipping and negative spread/inner edge semantics. |
| 16 group opacity | isolated offscreen layer | Two overlapping red children at group opacity .5; reference | M | Group opacity must be applied after child compositing; justify manifest bound before capture. |
| 17 filter order | ordered CSS filter chain | Blur/saturate/contrast/brightness order differs | F | Typed filter graph and intermediate color/edge domain required. |
| 18 drop shadow | alpha-shape shadow vs box shadow | Ring-shaped border; separate filtered/plain boxes | F | Distinguish source-alpha drop shadow from rectangular box shadow. |
| 19 backdrop filter | backdrop sampling, blur/saturate, rrect | Repeating scene background under translucent glass | F | Bind backdrop input/root, clip, border and filter bounds. |
| 20 nested backdrop root | opacity group plus backdrop filter | Child samples within `.root`, not whole page | F | Preserve root isolation, parent opacity and sampling region. |
| 21 multiply isolation | isolated blend group | Yellow/cyan overlap and `multiply`; reference | R | Add blend/isolation layer; independently derive exact overlap pixels. |
| 22 background blend | two gradients with `screen` | Background image stack and screen blend order | F | Preserve both gradients and per-background blend rather than element blend. |
| 23 polygon clip path | polygon path clip plus gradient | Ten-point authored polygon | A | Resolve polygon geometry, winding and AA clipping through both backends. |
| 24 gradient mask | radial alpha mask plus image | Mask stops and checker | A | Bind verified image resource and mask alpha/composition domain. |
| 25 mask composite | two masks with exclude | Solid linear mask and radial mask with 45%–47% transition | A | Implement continuous alpha exclusion `a + b − 2ab`, resolved mask mode/interpolation domain and balanced mask layer. |
| 26 SVG evenodd | inline SVG paths, evenodd, quadratic curve | Two `path` elements and exact SVG tree | A | Inline SVG must emit verified path commands; no silent image/background substitute. |
| 27 SVG stroke | path stroke/cap/join/dash | Three paths; round/square caps and zero-length dash | A | Stroke tessellation and dash phase need explicit parity. |
| 28 SVG filter | SVG blur/offset/color matrix | Filter region percentages, path and circle | F | Preserve SVG filter graph, bounds and offscreen intermediates. |
| 29 image sampling | two image draws, sampling, rotation | Checker twice; pixelated vs auto, `rotate(7deg)` | A | Verify decoded derivative, two image commands and rotated sampler semantics. |
| 30 object fit | image scale/crop/clip | Checker twice; contain vs cover, 70% 30%, rounded clip | A | Preserve intrinsic 80 × 80 size, object position and clipped crop. |
| 31 Latin shaping | ligatures, kerning, decoration | Serif text, italic/bold span, wavy underline; pinned fonts | T | No pinned font bytes/coverage or completed glyph-run/physical evidence. |
| 32 Hangul | Hangul/Jamo shaping and line breaking | `lang=ko`, keep-all, composed/decomposed text; fonts | T | Pin Korean face and validate clusters, fallback and line breaks. |
| 33 bidi | Arabic/Hebrew bidi with isolate | Two RTL paragraphs and `bdi`; fonts | T | Pin fonts and verify bidi runs, shaping and digit/isolate order. |
| 34 Indic | Devanagari shaping | Conjuncts/ligatures and `lang=hi`; fonts | T | Pin Devanagari face and verify glyph substitutions/positions. |
| 35 vertical writing | vertical-rl/lr layout and glyphs | Japanese/Korean text and two writing modes; fonts | T | Preserve vertical flow, orientation, breaks and font coverage. |
| 36 emoji fallback | fallback, variation, ZWJ clusters | Emoji sequences plus composed/decomposed Latin; fonts | T | Pin color/mono emoji faces and prove glyph/cluster coverage. |
| 37 flex gap | flex placement, opaque rects | Three items and 20px gap; reference | R | Verify source-computed positions and independent exact oracle, then capture. |
| 38 grid gap | grid track placement, opaque rects | 120/160 columns, 100/140 rows, 20px gap; reference | R | Verify track/position inventory and independent exact oracle, then capture. |
| 39 subgrid | parent grid and inherited tracks | Two rows share parent 100px/1fr/120px tracks | A | Resolve subgrid track sizing/placement before rectangle lowering. |
| 40 pseudo elements | generated before/after boxes | Empty `content`, two pseudo boxes; reference | R | Generated nodes must retain source/style identity; derive exact oracle. |
| 41 sticky scroll | nested scrollport, sticky/z-index, scrollbar paint | `#scroller` requested top 125 and descendant stripes | S | Apply element scroll and sticky placement/z-order; pin platform-independent scrollbar width, track/thumb colors and geometry, and reserved versus overlay space before an oracle. |
| 42 perspective | 3D transform, border, gradient | 600px perspective; rotateY 40/rotateX 20 | A | 3D matrix, projection and raster coverage absent from rectangle slice. |
| 43 paused animation | time-resolved transform/color | Manifest time 500ms; paused 1s animation with -.5s delay | S | Resolve keyframe interpolation at requested time; pin resulting transform/colors. |
| 44 glass dashboard | layered gradient, rrect, shadow, backdrop | Panel/cards/lines and translucent colors | F | Admit only after gradient, backdrop, border, shadow and order all survive. |
| 45 documentation layout | grid, text, border/rrect | Nav/main/code/note text and font-dependent layout | T | Pin fonts and line wraps; validate grid/text producer before effects. |
| 46 hero effects | conic gradient, blur, affine, shadow | Halo and rotated translucent plate | F | Combine typed conic/filter/transform/shadow with correct layer bounds. |
| 47 custom controls | rrect, border, gradient, inset, pseudo | Div-based field/button/toggle and `::after`; no GUI event | F | Preserve every Web style and generated knob; do not call this GUI input evidence. |
| 48 overflow ellipsis | text shaping, clipping, RTL ellipsis | LTR and Arabic RTL line boxes; fonts | T | Pin fonts and bidi widths; verify truncation side and ellipsis glyph. |

## Separate GUI lane

The `gui-button-16x16-v1` resting/pressed widget is **outside** this HTML corpus. Its input digest must bind the real widget/theme, button ID, label/action and pressed state; both states need changed completed pixels and the independent two-color exact oracle. Current GUI source/preflight and offline verifier evidence are candidates only. The physical GUI runner, trustworthy Simple spec and labeled-text/event path remain separate gates; case 47's styled HTML divs do not close them.

## Source-grounded caveats

The eight references exist only for cases 01, 06, 07, 16, 21, 37, 38 and 40. The 01 reference uses SVG paths to describe the expected result, but the **source** case consists of HTML divs; a reference SVG cannot replace its Web producer. The checker is the only external asset and appears in cases 13, 24, 29 and 30. The current upstream Skia provider preflights one GPU batch of opaque rectangles, optionally clipped, with an integer full-target first clear and rejects other command kinds/payloads. Case 01/06 candidate adapters are narrow; no evidence here extends them to the other 46 rows. The manifest's default `pinned-chromium-differential-not-spec-proof` and not-run status are preserved.

Inspected sources: `test/fixtures/html_css/corpus/{manifest.json,cases/*.html,references/*.html,assets/checker.svg}`, `src/lib/skia/backend/upstream_ganesh_vulkan/provider.spl`, `src/lib/gc_async_mut/gpu/browser_engine/web_opaque_box_qualification.spl`, `doc/05_design/simple_2d_skia_renderdoc_hardening.md`, and the case 01/06 and GUI physical qualification plans in this directory.
