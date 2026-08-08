# HTML/CSS SSpec Traceability

- status: fail
- reason: partial-static-pass-runtime-abi-probe-blocked
- behavioral audit: 2026-07-29
- canonical plan: doc/03_plan/sys_test/html_css_spec_traceability.md
- requirements: REQ-WEB-BROWSER-002, REQ-WEB-BROWSER-003, REQ-WEB-BROWSER-004, REQ-WEB-BROWSER-019, REQ-WEB-BROWSER-021
- execution status: evidence-blocked; no qualified target-runtime result
- raw checker HTML claim: 105/105; audited denominator is at least 113 and 8 are omitted
- raw checker W3C CSS property-like entries: 394 >= 390
- raw checker implemented CSS name claim: 284; functional count is unknown
- implemented CSS subset spec: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_generated_html_css_combinations_spec.spl
- unsupported CSS inventory spec: test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_inventory_traceability_spec.spl

## Landed Incremental Evidence

The following bounded tranches landed after the raw behavioral audit:

| Commit | Landed evidence | Independent result | Claim boundary |
|---|---|---|---|
| `28f0e779b0d2` | Canonical HTML owner changes, executable `html_element_traceability_spec.spl`, and its generated manual for `h1`–`h6`, `sub`, `sup`, valid-context fail-closed `selectedcontent`, and visible `slot` fallback | Static review PASS; generated manual complete with zero stubs | No qualified SSpec execution and no full HTML coverage claim |
| `b17e868199af` | Canonical CSS Grid declaration/style/layout/paint changes, executable `grid_foundation_wpt_spec.spl`, retained fixture/pinned manifest, truthful conformance checker updates, and generated manuals | Static review PASS; generated Grid and refreshed validator manuals complete with zero stubs | Bounded foundation only; retained corpus row remains `red-not-run`; no qualified SSpec execution and no full Grid/CSS claim |

Qualified execution remains blocked because the deployed pure-Simple wrapper
fails its bounded test-ABI admission probe. The one direct artifact attempt
segfaulted; its result was rejected, no Rust-seed/full-bootstrap fallback was
used, and it is not execution evidence for either tranche.

Overall status therefore remains RED/in progress. The pre-landed counts below
are retained as the audit baseline and have not been recomputed into a full
HTML or CSS behavioral denominator.

## Independent Behavioral Audit

The raw checker output below proves only that names occurred in broad text
roots at the audit baseline.
It does not execute SSpec, validate requirement tags or current manuals, or bind
names to canonical semantic/layout/DrawIR/Engine2D assertions.

- HTML Full: 12
- HTML Partial: 80
- HTML unsupported/fail-closed: 11
- HTML inventory-only: 2
- HTML elements omitted by checker inventory: 8 (`h1`–`h6`, `sub`, `sup`)
- CSS functionally proven count: unknown
- Claimed CSS properties absent from canonical declaration owners: at least 38
- Existing generated-combination source scenarios: 38
- Retained executed evidence: 13 pass / 25 fail
- Unsupported CSS: 92 production-relevant, 23 speech/aural-only,
  1 deprecated compatibility, 1 false nonproperty scrape
- Canonical manuals: stale and count-inconsistent
- Legacy duplicate manuals: stale

The raw `html_css_sspec_traceability_status=pass` value is retained below as
inventory evidence only and must not be promoted to behavioral PASS.

## Raw Evidence
- html_css_sspec_traceability_status=pass
- html_css_sspec_traceability_reason=pass
- html_css_sspec_traceability_html_url=https://html.spec.whatwg.org/multipage/indices.html
- html_css_sspec_traceability_css_url=https://www.w3.org/TR/CSS/
- html_css_sspec_traceability_html_tag_count=105
- html_css_sspec_traceability_required_html_tag_count=105
- html_css_sspec_traceability_html_tag_missing=
- html_css_sspec_traceability_css_property_count=394
- html_css_sspec_traceability_required_css_property_min_count=390
- html_css_sspec_traceability_css_property_missing_count=0
- html_css_sspec_traceability_css_property_missing=
- html_css_sspec_traceability_implemented_css_property_count=284
- html_css_sspec_traceability_implemented_css_property_indexed_count=277
- html_css_sspec_traceability_implemented_css_property_missing_count=0
- html_css_sspec_traceability_implemented_css_property_missing=
- html_css_sspec_traceability_unsupported_css_property_count=117
- html_css_sspec_traceability_unsupported_css_properties=all,azimuth,border-image,border-image-outset,border-image-repeat,border-image-slice,border-image-source,border-image-width,box-decoration-break,break-after,break-before,break-inside,clip-rule,color-interpolation-filters,column-fill,column-span,counter-increment,counter-reset,counter-set,elevation,flood-color,flood-opacity,glyph-orientation-vertical,grid-auto-columns,grid-auto-rows,grid-column-end,grid-row-end,hanging-punctuation,hyphenate-character,image-orientation,isolation,lighting-color,marker-side,mask,mask-border,mask-border-mode,mask-border-outset,mask-border-repeat,mask-border-slice,mask-border-source,mask-border-width,mask-clip,mask-composite,mask-image,mask-mode,mask-origin,mask-position,mask-repeat,mask-size,mask-type,mix-blend-mode,offset,offset-anchor,offset-distance,offset-path,offset-position,offset-rotate,overflow-anchor,page-break-after,page-break-before,page-break-inside,perspective,perspective-origin,pitch,pitch-range,play-during,property-name,rest,rest-after,rest-before,richness,scroll-margin,scroll-margin-block,scroll-margin-block-end,scroll-margin-block-start,scroll-margin-bottom,scroll-margin-inline,scroll-margin-inline-end,scroll-margin-inline-start,scroll-margin-left,scroll-margin-right,scroll-margin-top,scroll-padding,scroll-padding-block,scroll-padding-block-end,scroll-padding-block-start,scroll-padding-bottom,scroll-padding-inline,scroll-padding-inline-end,scroll-padding-inline-start,scroll-padding-left,scroll-padding-right,scroll-padding-top,scroll-snap-align,scroll-snap-stop,scroll-snap-type,shape-image-threshold,shape-margin,shape-outside,speak-as,speak-header,speak-numeral,speak-punctuation,speech-rate,stress,text-box,text-box-edge,text-box-trim,view-transition-name,voice-balance,voice-duration,voice-pitch,voice-range,voice-rate,voice-stress,voice-volume,volume
- html_css_sspec_traceability_unsupported_css_property_missing_count=0
- html_css_sspec_traceability_unsupported_css_property_missing=
- html_css_sspec_traceability_implemented_css_subset_spec=test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_generated_html_css_combinations_spec.spl
- html_css_sspec_traceability_unsupported_css_inventory_spec=test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_css_inventory_traceability_spec.spl

## Selected next rendering row (2026-07-31)

The next existing unsupported HTML/CSS row is **CSS viewport-fixed
positioning**, retained as RED in the canonical traceability plan. It has no
accepted implementation and requires its already-listed canonical layout, Draw
IR, Engine2D, pixel, and hit-testing evidence. This selection does not change
the row's RED classification, introduce requirements, or promote runtime/docgen
results.
