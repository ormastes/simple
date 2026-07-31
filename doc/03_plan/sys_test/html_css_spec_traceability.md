# HTML/CSS SSpec Traceability Test Plan

Status: RED / implementation and executable evidence required

## Requirements

- REQ-WEB-BROWSER-002: canonical HTML tokenizer/tree/semantics and safe fallback
- REQ-WEB-BROWSER-003: selected CSS cascade/layout/rendering profile
- REQ-WEB-BROWSER-004: Web semantic/layout to DrawIrComposition to Engine2D
- REQ-WEB-BROWSER-019: pinned conformance/corpus accounting
- REQ-WEB-BROWSER-021: executable SSpec and current mirrored manuals
- NFR-WEB-BROWSER-012: every claimed pinned test passes; unsupported rows remain visible
- NFR-WEB-BROWSER-017: stop after three verification/fix cycles

Requirements source:

`doc/02_requirements/feature/simple_web_browser_engine_production_hardening.md`

NFR source:

`doc/02_requirements/nfr/simple_web_browser_engine_production_hardening.md`

## Current authoritative audit

The generated 2026-07-29 report is inventory evidence, not executable
conformance evidence.

## Landed incremental evidence

The following bounded implementation and evidence tranches have landed since
the inventory audit:

| Commit | Bounded scope | Independent evidence | Evidence boundary |
|---|---|---|---|
| `28f0e779b0d2` | HTML defaults and behavior-first SSpec for `h1`–`h6`, `sub`, `sup`, `selectedcontent`, and `slot` | Independent static review PASS; canonical generated manual present and complete with zero stubs | Source/spec/manual evidence only; no qualified runtime execution is claimed |
| `b17e868199af` | CSS Grid foundation for explicit pixel tracks, gaps, placement, span, implicit row, block control, and over-quota fail-closed behavior; conformance manifest kept truthful | Independent static review PASS; canonical generated Grid manual and refreshed validator manual are complete with zero stubs | Bounded Grid foundation only; manifest remains `red-not-run`; no qualified runtime execution or full Grid/CSS claim |
| `b9e03cb9a487` | Inert `head`/`template` resource handling | Strengthened parsing-context SSpec and canonical manual | No qualified runtime execution |
| `543409eee861` | Safe fallback for ten embedded/media tags other than `iframe` | Semantic/resource/DrawIR/Engine2D control evidence | Bounded fallback only; corpus and qualified execution remain open |
| `7b3d40761352` | Hosted checkbox focus/input/click rendering | Semantic state, DrawIR geometry, and exact red-to-blue pixel controls | Bounded interaction only; qualified execution remains open |
| `ec39dc4ef85d` | Canonical `caption-side` declaration, style, table layout, DrawIR, and pixel behavior | Independent static PASS with focused spec/manual | Bounded property only; qualified execution remains open |
| `fc73115d0214` | Closed traceability gate and `property-name` exclusion | Fail-closed checker SSpec/manual | Behavioral counts remain zero without independent admission |
| `e62e8f5e9f6c` | Deterministic CSS/JavaScript animation frame trace | Initial/intermediate/pause/resume/completed DrawIR and pixel controls | Stage2 discovery blocked by the recorded parser error |
| `fb4050c3d2b` | `<article>` block default, `aspect-ratio`, CPU outline paint, SimpleScript/CSS DrawIR frame evidence, completed-animation frame reuse, and content-independent font metadata matching | High-capability root review; modern SSpecs and complete truthful manual mirrors; exact semantic/layout/DrawIR/pixel or scheduler-reuse controls | Bounded source/spec/manual evidence only; qualified pure-Simple execution and docgen remain pending |
| `b9e1a0e6707` | Selected medium-UA `<small>` sizing | Four exact semantic/style/layout/DrawIR/pixel steps and complete mirror | Static/source evidence held; qualified execution/docgen remain unavailable |
| `e7af94e921c` | Canonical DrawIR `text-transform` and RTL visual-text parity | Exact transformed command, literal-uppercase geometry/font payload, and full CPU-DrawIR pixel control | Static/source evidence held; no runtime or aggregate CSS PASS |
| `8beb64585b2` | Selected `<abbr>` inline-flow behavior through canonical text rendering | Static semantic/style/layout/DrawIR/pixel scenario and current mirror | Static/source evidence held; qualified execution/docgen remain unavailable |
| `2078c3dfab4` | Duplicate-offset CSS keyframes cascade in source order | Unit proof preserves a distinct earlier property while the later color wins; four exact scheduler/DrawIR/Engine2D steps and current mirror | Static/source evidence held; qualified runtime execution remains unavailable |
| `0e4b75b167b` | CSS implicit per-property keyframe endpoints and discrete incompatible-value interpolation | Unit controls plus a four-step scheduler/DrawIR/Engine2D scenario and complete static mirror | Static/source evidence held; qualified execution/docgen remain unavailable |
| `7b290473ae6` | Selected `<time>` inline-flow behavior through canonical text rendering | Static semantic/style/layout/DrawIR/pixel scenario with span parity and forced-block control | Static/source evidence held; qualified execution/docgen remain unavailable |
| `08de37b0902` | CSS logical size/min/max mapping through horizontal, vertical, and sideways writing modes | Two modern scenarios cover inherited/important winners, authored order, exact DrawIR geometry, and discriminating Engine2D pixels; complete static mirror | Static/source evidence held; qualified execution/docgen remain unavailable |
| `771dfb23835b` | Canonical iframe Draw IR embedding design | Reviewed architecture/detail/agent plans | Design only; no iframe implementation claim |
| current `<code>` lane | Selected UA monospace family with authored sans-serif override | Exactly four-step SSpec covers semantic parentage, inline/monospace computed style, resolved DrawIR font family/identity and origin, explicit-monospace parity, sans override, and discriminating Engine2D frames | Source/spec/handwritten-manual evidence only; qualified execution/docgen remain open |
| current `<kbd>`/`<samp>`/`<var>` lane | Selected inline monospace and italic UA typography with authored overrides | Exactly four-step SSpec covers grouped semantic parentage, computed styles, control geometry, DrawIR font/style metadata and origin, explicit-style parity, authored override winners, and discriminating Engine2D frames | Source/spec/handwritten-manual evidence only; `pre` whitespace behavior and qualified execution/docgen remain open |
| Current `<hr>` lane | Native `hr` void semantics and selected UA separator defaults | Exactly four-step SSpec covers semantic identity, UA style/geometry, exact `0`/`0px`/`none`/`hidden` border clearing, mixed-invalid/missing preservation, DrawIR, and exact Engine2D control pixels | Source/spec/manual evidence only; qualified pure-Simple execution remains required |
| current change | Selected deterministic `fieldset`/`legend` UA defaults and authored-style rendering | Isolated semantic parentage, four-side `border:none`/`0` clearing, exact DrawIR geometry, exact Engine2D/control pixels, and handwritten draft manual | Bounded fallback only; special legend formatting/cutout, disabled propagation, admitted docgen, and qualified execution remain open |
| current definition-list lane | Cross-kind omitted-end-tag repair plus selected `dl`/`dt`/`dd` UA defaults | Exactly four-step SSpec covers sibling identity, UA and authored margins, exact DrawIR geometry, and exact Engine2D component/control pixels | Source/spec/handwritten-manual evidence only; admitted docgen, qualified execution, and corpus accounting remain open |
| current `blockquote` lane | Selected four-side UA margins through canonical layout and pixels | Exactly four-step SSpec covers semantic body parentage, selected UA margins, exact DrawIR geometry, and exact Engine2D component/control pixels | Source/spec/handwritten-manual evidence only; qualified execution remains open |
| current `header` lane | Selected block default through canonical layout and pixels | Exactly four-step SSpec covers semantic body parentage, `display:block`, exact DrawIR geometry, and exact Engine2D component/control pixels | Source/spec/handwritten-manual evidence only; qualified execution remains open |
| current `address` lane | Selected block/italic UA presentation plus direct/full normal overrides | Exactly four-step SSpec covers semantic body parentage, both style paths, absolute WebIR/DrawIR geometry, and discriminating Engine2D/control pixels | Source/spec/handwritten-manual evidence only; grouped HTML coverage and qualified execution remain open |
| current `details`/`summary` lane | First-summary disclosure semantics, default closed/open marker, and canonical click default action | One four-step marker scenario plus the existing four-step disclosure scenario cover UA and authored `list-item` through fast dispatch, authored-`block` suppression, marker-slot geometry, exact marker DrawIR state, closed/open/equal-authored/suppressed Engine2D pixels, closed/open/nested content, and click default action | Bounded fallback still omits the synthesized shadow summary; qualified execution remains open |
| current `figure` lane | Selected four-side UA margins through canonical layout and pixels | Exactly four-step SSpec covers semantic body parentage, selected UA margins, exact DrawIR geometry, and exact Engine2D component/control pixels | Source/spec/handwritten-manual evidence only; caption semantics and qualified execution remain open |
| current `menu` lane | Selected LTR list-container spacing through canonical layout and pixels | Exactly four-step SSpec covers semantic body parentage, selected UA padding/margins, exact DrawIR geometry, and exact Engine2D component/control pixels | Source/spec/handwritten-manual evidence only; markers, RTL logical padding, full menu semantics, and qualified execution remain open |
| current CSS `gap:0` lane | Later zero shorthand resets an earlier positive Flex gap through dispatch and full Style reconstruction | Exactly four-step SSpec covers computed gap fields, adjacent Web layout boxes, canonical DrawIR rectangles, and all 48 Engine2D pixels | Source/spec/handwritten-manual evidence only; qualified execution/docgen remain open |
| current CSS `outline:0` lane | Later zero shorthand suppresses an earlier positive outline through dispatch and full Style reconstruction | Exactly four-step SSpec covers computed outline width, unchanged Web layout boxes, canonical DrawIR style/rectangles, and all 60 Engine2D pixels | Source/spec/handwritten-manual evidence only; full outline grammar and qualified execution/docgen remain open |
| current CSS `flex-basis:0` lane | Later zero basis clears an earlier positive Flex basis through dispatch and full Style reconstruction | Exactly four-step SSpec covers computed basis, exact WebIR-derived layout/DrawIR boxes, and all 40 Engine2D pixels | Source/spec/handwritten-manual evidence only; full basis grammar and qualified execution/docgen remain open |

These commits correct the named source/spec/manual gaps but do not close the
overall HTML/CSS traceability goal. The deployed pure-Simple wrapper still
fails its bounded test-ABI admission probe; the one direct artifact attempt
segfaulted and was not accepted. Until a qualified pure-Simple target binary
runs the scenarios, both tranches remain execution-evidence-blocked.

### HTML

The source inventory began with 80 Partial rows. The bounded `code`, `kbd`,
`samp`, `var`, `hr`,
fieldset/legend, definition-list, `article`, blockquote, `header`,
`details`/`summary`, `figure`, `menu`, `small`, `abbr`, and `time` lanes
reclassify those twenty named rows into their own fallback rows, leaving 60 in the
undifferentiated Partial backlog.
The two rows called out as
inventory-only or missing were subsequently covered by `28f0e779b0d2`.
No named row appears in both a bounded row and the remaining Partial count.

| Classification | Count | Meaning |
|---|---:|---|
| Full | 12 | Direct semantic/tree plus applicable layout/DrawIR/Engine2D or hidden/fail-closed evidence |
| Partial remaining | 60 | Tag appears in text/grouped render coverage but lacks isolated end-to-end proof; excludes `code`,`kbd`,`samp`,`var`,`hr`,`fieldset`,`legend`,`dl`,`dt`,`dd`,`article`,`blockquote`,`header`,`details`,`summary`,`figure`,`menu`,`small`,`abbr`,`time` |
| Bounded selected-profile fallback | 20 | `code`,`kbd`,`samp`,`var`,`hr`,`fieldset`,`legend`,`dl`,`dt`,`dd`,`article`,`blockquote`,`header`,`details`,`summary`,`figure`,`menu`,`small`,`abbr`,`time`; basic UA/cascade/DrawIR/pixel paths covered, while special formatting and aggregate conformance remain Partial/RED |
| Unsupported/fail-closed | 11 | Embedded/media/native semantics are not implemented |
| Inventory-only before landed tranche | 2 | `selectedcontent`, `slot`; bounded behavior landed |
| Missing before landed tranche | 8 | `h1`–`h6`, `sub`, `sup`; bounded behavior landed |

Full rows currently identified:

`html, head, meta, title, body, main, p, div, section, table, textarea, template`

Historically unsupported/fail-closed rows:

`area, audio, canvas, embed, iframe, map, object, picture, source, track, video`

Former inventory-only rows:

`selectedcontent, slot`

The old checker’s published `105/105` denominator remains insufficient as a
behavioral PASS claim even though the ten named omissions now have bounded
source/spec/manual evidence.

### CSS

- Published implemented count: 284.
- Functional count: not proven.
- Existing generated-combination scenarios: 38 source scenarios; retained
  evidence records 13 passing and 25 failing.
- Exactly 36 claimed properties are not recognized by canonical renderer
  declaration owners after counting lookups through every local declaration
  table variable.
- Only 43 behavioral cases exist for the 284 claimed names.
- Several claimed properties are metadata-only and have no layout/raster
  consumer.
- Invalid declarations and CSS-wide keywords do not have one correct
  cross-stage cascade owner.
- Actual modern CSS system specs under
  `test/03_system/feature/web_platform/css/` are excluded from the current
  checker roots.

Unsupported inventory partition:

| Class | Count | Policy |
|---|---:|---|
| Production visual/layout/interaction | 92 | RED implementation backlog |
| Speech/aural-only | 23 | Explicitly unsupported outside a TTS/accessibility owner |
| Deprecated compatibility | 1 | `glyph-orientation-vertical`; possible audited alias only |
| False scrape/nonproperty | 1 | Remove `property-name` from property inventory |

No unsupported name counts as implemented merely because it occurs in prose,
an inventory literal, an `@supports` table, or metadata.

## Current traceability matrix

| REQ/NFR | Row/group | Support | Executable spec/scenario | Production owners | Required oracle | Manual/result | Status |
|---|---|---|---|---|---|---|---|
| REQ-002/004/019/021 | HTML Full 12: `html,head,meta,title,body,main,p,div,section,table,textarea,template` | Full by static audit | `test/03_system/feature/web_platform/html/html_parsing_contexts_spec.spl`; browser production-hardening spec | tokenizer/tree, BrowserSession semantic tree, HTML layout renderer, DrawIR, Engine2D | exact tag/parent/style/geometry/commands/pixels or hidden absence | canonical manuals exist; qualified execution unavailable | Evidence-blocked |
| REQ-002/004/019/021 | HTML Partial 60 remaining; twenty bounded rows split below | Partial | grouped text/tag and bitmap matrices; exact scenario mapping missing | same canonical owners | per-group identity, UA defaults, geometry, DrawIR, pixels | new grouped specs/manuals required | RED |
| REQ-002/004/021 | HTML `article` | Bounded block-default behavior landed in `fb4050c3d2b` | `article_element_rendering_spec.spl`: `should lower the article block default through Draw IR to pixels` | tokenizer/tree, canonical UA defaults, Web layout, DrawIR, Engine2D | semantic parentage, `display:block`, exact geometry and component/control pixels | complete handwritten mirror; qualified docgen/execution unavailable | Evidence-blocked |
| REQ-002/003/004/021 | HTML `address` selected profile | Bounded block/italic UA presentation in current lane | `address_element_rendering_spec.spl`: `should lower address UA typography and both overrides to pixels` | tokenizer/tree, canonical UA defaults and declaration dispatch/full owners, Web layout/WebIR, DrawIR, Engine2D | semantic parentage, block/italic default, normal override parity, `[0,0,80,16]` geometry, exact command metadata and pixels/control frames | handwritten complete mirror; grouped HTML coverage and qualified execution unavailable | Evidence-blocked |
| REQ-002/004/021 | HTML `code` selected profile | Bounded native inline monospace behavior in current lane | `code_element_rendering_spec.spl`: `should lower the code UA monospace font through Draw IR to pixels` | tokenizer/tree, canonical UA defaults/cascade, Web layout, DrawIR text owner, Engine2D | semantic body parent, inline display, default/explicit monospace parity, authored sans-serif override, resolved font identity, geometry, and discriminating pixels | handwritten complete mirror; qualified execution/docgen unavailable | Evidence-blocked |
| REQ-002/004/021 | HTML `kbd`,`samp`,`var` selected profile | Bounded grouped UA typography in current lane | `kbd_samp_var_rendering_spec.spl`: `should lower grouped UA typography through Draw IR to pixels` | tokenizer/tree, canonical inline/tag defaults/cascade, Web layout, DrawIR text owner, Engine2D | grouped semantic parentage, inline display, monospace and italic defaults, authored overrides, control geometry, resolved font/style metadata, and discriminating pixels | handwritten complete mirror; `pre` whitespace behavior and qualified execution/docgen unavailable | Evidence-blocked |
| REQ-002/003/004/019/021 | HTML `hr` | Bounded behavior in current lane | `test/03_system/feature/web_platform/html/hr_element_wpt_spec.spl`: `should render hr defaults and author CSS through Engine2D` | canonical tree, tag defaults, shared declaration application, Web layout, DrawIR, Engine2D | void identity, selected 8 px margins and 1 px gray border, exact `border:0`/`0px`/`none`/`hidden` clearing, mixed digit-bearing invalid/missing preservation, authored red geometry, exact component/control pixels | mirrored manual generated in current lane; qualified execution unavailable | Evidence-blocked |
| REQ-002/019/021 | HTML embedded/media fallback 10: `area,audio,canvas,embed,map,object,picture,source,track,video` | Bounded fail-closed fallback landed in `543409eee861` | safe embedded/media fallback spec | tokenizer/tree/resource fallback, Web layout, DrawIR, Engine2D | semantic/resource exclusion plus deterministic fallback commands and pixels | canonical spec/manual; qualified execution unavailable | Evidence-blocked |
| REQ-002/004/019/021 | HTML `iframe` | Bounded reviewed inert-`srcdoc` source tranche | `test/02_integration/rendering/simple_web_iframe_draw_ir_embedding_spec.spl` | canonical child Web composition to DrawIR embedding | order, clip, offsets, IDs, materials, exact pixels, deadline/rules, cleared child hits | handwritten mirror; legacy pixel parity and qualified execution unavailable | STATIC REVIEW PASS / RED migration boundary |
| REQ-002/019/021 | Inert `head`/`template` resources | Bounded behavior landed in `b9e03cb9a487` | strengthened HTML parsing-context scenario | tokenizer/tree/resource discovery | inert descendants excluded from fetch/resource output | canonical manual; qualified execution unavailable | Evidence-blocked |
| REQ-002/004/006/021 | Hosted checkbox interaction/rendering | Bounded behavior landed in `7b3d40761352` | hosted form interaction scenario | DOM/event/focus/style/layout/DrawIR/Engine2D | semantic parentage, state transition, geometry, exact red-to-blue pixels | canonical manual; qualified execution unavailable | Evidence-blocked |
| REQ-002/019/021 | HTML formerly inventory-only 2: `selectedcontent,slot` | Bounded behavior landed in `28f0e779b0d2` | `html_element_traceability_spec.spl`: valid-context fail-closed `selectedcontent` plus visible inline `slot` fallback | tokenizer/tree/template/slot owners | deterministic semantic/fallback behavior, DrawIR, pixels/control | canonical manual complete; independent static PASS; runtime unavailable | Evidence-blocked |
| REQ-002/019/021 | HTML formerly omitted 8: `h1`–`h6`,`sub`,`sup` | Bounded behavior landed in `28f0e779b0d2` | `html_element_traceability_spec.spl`: headings and inline baseline scenarios | tokenizer/tree/style/layout/DrawIR/Engine2D | UA defaults and exact geometry/pixels | canonical manual complete; independent static PASS; runtime unavailable | Evidence-blocked |
| REQ-002/003/004/021 | HTML `fieldset`,`legend` selected profile | Bounded fallback; special legend formatting/cutout and disabled propagation remain Partial/RED | `fieldset_legend_rendering_spec.spl`: `should trace selected fieldset and legend semantics to exact pixels` | tokenizer/tree, canonical UA defaults/cascade/layout, DrawIR, Engine2D | parentage, UA defaults, four-side `border:none`/`0` clearing, authored CSS, exact geometry, exact component/control pixels | handwritten draft mirror only; admitted docgen and qualified execution unavailable | Evidence-blocked / Partial-RED boundary |
| REQ-002/003/004/021 | HTML `dl`,`dt`,`dd` selected profile | Bounded definition-list behavior | `definition_list_rendering_spec.spl`: `should trace definition-list semantics and styles to exact pixels` | tokenizer/tree, canonical UA defaults/cascade/layout, DrawIR, Engine2D | cross-kind omitted-end-tag sibling repair, selected margins, authored override, exact geometry and component/control pixels | handwritten draft mirror only; admitted docgen and qualified execution unavailable | Evidence-blocked |
| REQ-002/004/021 | HTML `blockquote` selected profile | Bounded UA-default behavior | `blockquote_element_rendering_spec.spl`: `should lower blockquote UA margins through Draw IR to pixels` | tokenizer/tree, canonical UA defaults/layout, DrawIR, Engine2D | semantic body parent, all four selected UA margins, exact geometry, DrawIR, and component/control pixels | handwritten complete mirror; qualified execution unavailable | Evidence-blocked |
| REQ-002/004/021 | HTML `header` selected profile | Bounded block-default behavior | `header_element_rendering_spec.spl`: `should lower the header block default through Draw IR to pixels` | tokenizer/tree, canonical UA defaults, Web layout, DrawIR, Engine2D | semantic body parent, `display:block`, exact geometry, DrawIR, and component/control pixels | handwritten complete mirror; qualified execution unavailable | Evidence-blocked |
| REQ-002/004/021 | HTML `figure` selected profile | Bounded UA-default behavior landed in `897368fb592` | `figure_element_rendering_spec.spl`: `should lower figure UA margins through Draw IR to pixels` | tokenizer/tree, canonical UA defaults/layout, DrawIR, Engine2D | semantic body parent, all four selected UA margins, exact geometry, DrawIR, and component/control pixels | complete mirror; static evidence held, caption semantics and qualified execution unavailable | Evidence-blocked |
| REQ-002/004/021 | HTML `menu` selected profile | Bounded UA-default behavior | `menu_element_rendering_spec.spl`: `should lower menu UA list spacing through Draw IR to pixels` | tokenizer/tree, canonical UA defaults/layout, DrawIR, Engine2D | semantic body parent, selected LTR list padding/margins, exact geometry, DrawIR, and component/control pixels | handwritten complete mirror; markers, RTL logical padding, full menu semantics, and qualified execution unavailable | Evidence-blocked |
| REQ-002/004/021 | HTML `small` selected profile | Bounded medium-UA `font-size:smaller` behavior | `small_element_rendering_spec.spl`: `should lower the small UA font size through Draw IR to pixels` | tokenizer/tree, canonical UA defaults/inline baseline layout, DrawIR, Engine2D | semantic body parent, inline display, 16-to-13 px selected size, exact geometry/text command, absolute repaired-box pixels | handwritten complete mirror; fractional sizing, broad line-height combinations, and qualified execution unavailable | Evidence-blocked |
| REQ-002/004/021 | HTML `abbr` selected profile | Bounded native inline-flow behavior landed in `8beb64585b2` | `simple_web_renderer_spec.spl`: bounded `<abbr>` semantic/style/layout/DrawIR/pixel scenario | tokenizer/tree, canonical UA defaults/inline layout, DrawIR text owner, Engine2D | semantic identity, inline display, sibling flow, exact text command/geometry, and discriminating pixels | current mirror; static evidence held, qualified execution unavailable | Evidence-blocked |
| REQ-002/004/021 | HTML `time` selected profile | Bounded native inline-flow behavior landed in `7b290473ae6` | `simple_web_renderer_spec.spl`: `keeps time in canonical inline flow` | tokenizer/tree, canonical UA defaults/inline layout, DrawIR text owner, Engine2D | semantic identity, inline display, sibling flow, exact text geometry/advances, span pixel parity, and forced-block inequality | current mirror; static evidence held, qualified execution unavailable | Evidence-blocked |
| REQ-003/004/019/021 | CSS claimed 284 | Functional count unknown | generated-combinations spec has 38 scenarios | declaration/cascade/style/layout/paint/DrawIR/Engine2D | isolated semantic, layout, DrawIR, pixel baseline/control | retained 13 pass/25 fail; manuals stale | FAIL |
| REQ-003/004/019/021 | CSS Grid bounded foundation | Bounded behavior landed in `b17e868199af` | `test/03_system/feature/web_platform/css/grid_foundation_wpt_spec.spl` | canonical declaration/style/layout/paint-layout, DrawIR, Engine2D | exact tracks, placement/span/implicit-row geometry and pixels; block and quota controls | canonical manual complete; independent static PASS; manifest `red-not-run`; runtime unavailable | Evidence-blocked |
| REQ-003/004/005/006/007/017/021 | CSS/JavaScript/SimpleScript animation frame trace | Bounded initial/intermediate/completed, pause/resume, JavaScript and SimpleScript document-origin frame alignment, SimpleScript style-frame, completed-frame reuse, duplicate-offset source-order cascade, and implicit per-property endpoint behavior implemented | `request_animation_frame_alignment_spec.spl`: JavaScript alignment; `event_loop_spec.spl`: staggered and nested SimpleScript scheduling; `browser_session_script_css_animation_spec.spl`: red-before/blue-at-16 SimpleScript Draw IR/Engine2D trace and deterministic JavaScript trace; `animations_wpt_spec.spl`: completed-frame reuse and implicit endpoints | BrowserSession monotonic clock/DOM bridge, canonical SimpleScript EventLoop deadline, JavaScript timer owner, keyframe parser/CSS animation instances, render-session cache, canonical HTML layout/DrawIR, Engine2D | exact scheduler deadlines, stage geometry/colors/pixels, same-offset declaration union/winner, per-property underlying endpoints, discrete incompatible values, and unchanged paint count/checksum after completion | complete manual mirrors; JavaScript and SimpleScript clocks are distinct implementations of one 16ms document-origin contract; qualified execution/docgen unavailable | Evidence-blocked |
| REQ-003/004/021 | CSS logical sizing and writing mode | Bounded nonnegative integer-pixel behavior landed in `08de37b0902` | `logical_sizing_writing_mode_spec.spl`: maps logical sizes through writing mode and preserves empty-cell cascade winners | declaration/cascade/style/layout, canonical DrawIR, Engine2D | horizontal/vertical/sideways size and min/max axes, inherited/normal/important winners, authored physical/logical order, exact geometry, and discriminating pixels | complete static mirror; qualified execution/docgen unavailable | Evidence-blocked |
| REQ-003/004/021 | CSS `aspect-ratio` | Bounded width-led and height-led behavior landed in `fb4050c3d2b` | `aspect_ratio_wpt_spec.spl` | declaration/style/layout, DrawIR, Engine2D | exact 32×16 and 12×24 geometry, retained computed style, exact color pixels, zero skipped commands | complete handwritten mirror; qualified docgen/execution unavailable | Evidence-blocked |
| REQ-003/004/021 | CSS `outline` / `outline-offset` CPU route | Bounded canonical CPU DrawIR paint landed in `fb4050c3d2b` | `simple_web_css_box_effects_spec.spl`: `should apply cascaded outline offset through Draw IR to CPU pixels` | declaration/cascade, paint-layout DrawIR, canonical CPU DrawIR executor | retained width/offset plus exact displaced outline and interior-control pixels | complete handwritten mirror; qualified docgen/execution unavailable | Evidence-blocked |
| REQ-003/004/021 | CSS `outline:0` cascade reset | Bounded shorthand correction in current lane | `test/03_system/feature/web_platform/css/outline_zero_cascade_spec.spl`: `should suppress earlier outlines through both declaration paths` | canonical declaration dispatch/full owners, Style, Web layout, DrawIR, Engine2D | zero computed outline width, exact unchanged geometry/commands, full 60-pixel framebuffer without the prior red ring | handwritten mirror; full outline grammar and qualified execution/docgen unavailable | Evidence-blocked |
| REQ-003/004/021 | CSS `text-transform` DrawIR route | Bounded canonical visual-text repair landed in `e7af94e921c` | `simple_web_renderer_spec.spl`: `lowers text-transform through Draw IR to exact uppercase pixels` | computed style, canonical DrawIR text owner, font metrics, CPU DrawIR executor | exact `uppercase` style, `MIX-WIDE` command value, literal-uppercase geometry/family/identity/advances, full-frame pixel equality, lowercase control inequality | complete mirror; static evidence held, qualified execution unavailable | Evidence-blocked |
| REQ-003/004/021 | CSS `gap:0` cascade reset | Bounded Flex shorthand correction in current lane | `test/03_system/feature/web_platform/css/flex_gap_zero_cascade_spec.spl`: `should reset positive Flex gaps through both declaration paths` | canonical declaration dispatch/full owners, Style, Web layout, DrawIR, Engine2D | zero computed shorthand/axis fields, exact adjacent geometry/commands, full 48-pixel framebuffer | handwritten mirror; qualified execution/docgen unavailable | Evidence-blocked |
| REQ-003/004/021 | CSS `flex-basis:0` cascade reset | Bounded longhand correction in current lane | `test/03_system/feature/web_platform/css/flex_basis_zero_cascade_spec.spl`: `should clear positive Flex bases through both declaration paths` | canonical declaration dispatch/full owners, Style, Web layout/WebIR, DrawIR, Engine2D | zero computed basis, exact two-pixel reset/control geometry and commands, full 40-pixel framebuffer | handwritten mirror; full basis grammar and qualified execution/docgen unavailable | Evidence-blocked |
| REQ-003/004/019/021 | CSS claimed but unrecognized, 36 source diagnostics | False implemented claim | checker regression records exact source diagnostic; behavioral scenarios missing | canonical declaration dispatch and downstream owners | valid/invalid/inherited style plus discriminating render | checker manual current; behavior evidence missing | FAIL |
| REQ-003/004/019/021 | CSS `caption-side` | Bounded behavior landed in `ec39dc4ef85d` | focused table caption scenario | canonical declaration/style/table layout/DrawIR/Engine2D | top/bottom geometry and exact pixels with control | canonical manual; independent static PASS; qualified execution unavailable | Evidence-blocked |
| REQ-003/004/019/021 | CSS `border-spacing` | Bounded separated-border implementation in current change; collapsed-border behavior is tracked separately below | focused fixed/automatic table scenario plus zero-spacing control in `table_formatting_spec.spl` | canonical declaration/style/table layout/DrawIR/Engine2D | one/two nonnegative pixel values, CSS-wide handling, exact gap geometry and pixels | canonical manual current; Stage2 build passed but runtime segfaulted before assertions | Evidence-blocked |
| REQ-003/004/019/021 | CSS unsupported production 92 | Unsupported backlog | inventory spec is name-only | owners named by lane below | executable fail-closed or full four-oracle chain | manual stale; no behavior PASS | RED |
| REQ-003/019/021 | CSS speech/aural 23 | Explicit scope exclusion | fail-closed/nonvisual scenario missing | future TTS/accessibility owner | no false visual support claim | missing | RED |
| REQ-003/019/021 | Deprecated `glyph-orientation-vertical` | Unsupported/alias candidate | missing | declaration alias owner if selected | audited equality with `text-orientation` | missing | RED |
| REQ-003/019/021 | False `property-name` scrape | Nonproperty | closed checker regression in `fc73115d0214` | traceability checker | excluded from CSS denominator and unrecognized list | canonical manual; qualified execution unavailable | Evidence-blocked |
| AC-3 / REQ-004/019/021 | Generated-GUI HTML/CSS combinations | Partial/failing | `simple_web_generated_html_css_combinations_spec.spl`: `renders generated GUI semantic panels with flex, padding, border, and text styles` plus 37 related scenarios | GUI HTML producer, canonical Web semantic/style/layout, DrawIR, Engine2D | producer HTML identity, semantic parent/style, exact geometry/commands/pixels, block control | canonical manual stale; retained aggregate 13 pass/25 fail | FAIL |
| NFR-012/017 | Aggregate execution/manual evidence | Evidence-blocked | manifest traceability spec is stale | checker/runner/docgen | qualified SHA, executed/pass/fail, source/manual hashes, zero stubs | absent | FAIL |

Every named group expands to one matrix record per element/property before
behavioral PASS. Group rows are explicit backlog accounting, not completion.

## Traceability matrix schema

Every claimed HTML element or CSS property row must contain:

| Field | Required evidence |
|---|---|
| REQ | One or more REQ-WEB-BROWSER IDs |
| Name | Exact element/property |
| Support status | Full, Partial, Unsupported/fail-closed, Missing |
| Executable spec | Canonical `test/..._spec.spl` path |
| Scenario | Exact `it "should ..."` description |
| `@req` | Present in executable source |
| Production path | Canonical parser/style/layout/DrawIR/Engine2D owners |
| Semantic oracle | DOM/tag/attribute/computed-style identity |
| Layout/DrawIR oracle | Stable ID, parentage, geometry, clip, order, style |
| Engine2D oracle | Exact discriminating pixels/count/checksum when visible |
| Negative/control | Baseline, invalid, fallback, or unsupported behavior |
| Runner evidence | Qualified binary path and SHA-256 |
| Result | Executed/pass/fail counts |
| Manual | Canonical mirrored `doc/06_spec/...md`, source hash, zero stubs |
| Upstream pin | WHATWG/W3C URL, retrieval date, retained content hash |
| Corpus pin | WPT/corpus row ID, revision/hash, retained evidence path |
| Status/blocker | Explicit; no inferred PASS |

Name presence alone satisfies none of the behavior columns.

## Frozen displayed steps

- `Verify executable HTML and CSS traceability`
- `Trace HTML elements through Web semantics and Draw IR`
- `Trace implemented CSS properties through canonical rendering`
- `Classify unsupported CSS properties without false implementation claims`

The bounded `fieldset`/`legend` scenario has exactly these four visible steps:

- `Parse fieldset and legend as a semantic parent-child pair`
- `Apply selected user-agent defaults before authored CSS`
- `Lower authored fieldset and legend boxes to exact Draw IR geometry`
- `Rasterize exact component pixels against an unstyled control`

The bounded definition-list scenario has exactly these four visible steps:

- `Parse omitted dt and dd end tags as definition-list siblings`
- `Apply definition-list user-agent defaults before authored CSS`
- `Lower authored definition-list boxes to exact Draw IR geometry`
- `Rasterize exact definition-list pixels against a plain control`

The bounded `figure` scenario has exactly these four visible steps:

- `Parse figure as a body child`
- `Apply selected figure user-agent margins`
- `Lower the figure box to exact Draw IR geometry`
- `Rasterize the Draw IR figure box`

Its frozen setup/checker helpers are `_figure_html`, `_node_index`, `_command`,
`_style`, `_geometry`, `_check_figure_semantics`, `_check_figure_ua_style`,
`_check_figure_draw_ir`, and `_check_figure_pixels`.

The bounded `menu` scenario has exactly these four visible steps:

- `Parse menu as a body child`
- `Apply selected menu user-agent list spacing`
- `Lower the menu box to exact Draw IR geometry`
- `Rasterize the Draw IR menu box`

Its frozen setup/checker helpers are `_menu_html`, `_node_index`, `_command`,
`_style`, `_geometry`, `_color_count`, `_check_menu_semantics`,
`_check_menu_ua_style`, `_check_menu_draw_ir`, and `_check_menu_pixels`.

## Implementation-ready first tranche

### HTML omitted and inventory-only elements

Spec:

`test/03_system/feature/web_platform/html/html_element_traceability_spec.spl`

Scenarios:

- `should retain h1 through h6 as block headings in source order`
- `should keep sub and sup in inline flow with distinct baselines`
- `should fail closed for selectedcontent and render slot fallback inline`

Helpers:

- `_expect_semantic_identity`
- `_expect_exact_draw_ir_geometry`
- `_render_pixels`
- `_node_index`, `_command`, `_style`, `_count_color`

Production owners:

- `src/lib/gc_async_mut/gpu/browser_engine/html_tokenizer.spl`;
- `src/lib/gc_async_mut/gpu/browser_engine/html_tree_builder.spl`;
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`;
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_style.spl`;
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_declarations.spl`;
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`;
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout.spl`;
- `src/os/compositor/compositor_engine2d.spl`.

Frozen oracles:

- 16px medium, half-up heading defaults `(font, margin)`:
  h1 `(32,21)`, h2 `(24,20)`, h3 `(19,19)`, h4 `(16,21)`,
  h5 `(13,22)`, h6 `(11,26)`;
- each isolated heading geometry is `[0, margin, 96, font]`, with exact
  independently computed background area and matching DrawIR geometry;
- inline control `[0,8,8,16]`, sub `[8,12,7,13]`,
  sup `[15,4,7,13]`, line-height normal and ±4 baseline offsets;
- selectedcontent is tested only in valid select/button structure as an
  explicitly unsupported fail-closed row with zero unique red glyph pixels;
- slot control geometry `[0,32,104,16]`, inline fallback text, computed
  foreground `4286331629`, and matching unique purple glyph pixels.

REQ-019 binds the retained HTML profile fixture row and SHA-256
`bd8cba62a4ed894e8a5ef3636c7f657ae974ecda1eb4da401d535b5279131e84`,
including an altered-row negative.

Current expected result: the named UA-default owners, executable source, and
canonical manual landed in `28f0e779b0d2` and passed independent static review.
The tranche remains evidence-blocked until qualified execution passes; it does
not establish full HTML coverage.

### HTML horizontal rule

Spec:

`test/03_system/feature/web_platform/html/hr_element_wpt_spec.spl`

Scenario:

- `should render hr defaults and author CSS through Engine2D`

Canonical production owners:

- `src/lib/gc_async_mut/gpu/browser_engine/html_tree_builder.spl`;
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_declarations.spl`;
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`;
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout.spl`;
- `src/os/compositor/compositor_engine2d.spl`.

Frozen oracles:

- `hr` remains a childless `hr` semantic node under `body`;
- selected UA style is block with 8 px top/bottom margins and four 1 px
  `0xFF808080` border sides;
- default DrawIR geometry is `[0,8,64,2]`;
- authored CSS replaces those defaults with border/margins zero and
  `[0,0,32,4]` red geometry;
- exact `border:0px`, `border:none`, and `border:hidden` also clear all four
  sides, while mixed invalid `border:0 1bogus` and `border:0 url(1)` plus a
  missing declaration preserve the selected UA sides;
- Engine2D paints exactly 128 gray control pixels or 128 red authored pixels
  inside the matching component rectangle and zero matching pixels outside.

REQ-019 binds the retained `whatwg-html-hr` row dated `2026-07-30` with
SHA-256 `8e210d74a27b9e386affe055a865d611fe92109862143287c75dfb7be689780a`
and an altered-row negative. This row remains evidence-blocked until a
source-admitted pure-Simple runner executes the scenario.

### CSS grid foundation

Spec:

`test/03_system/feature/web_platform/css/grid_foundation_wpt_spec.spl`

Scenarios:

- `should lower explicit tracks placement span and an implicit row`
- `should keep the equivalent block control in vertical flow`

Helpers:

- `_grid_command_index`
- `_grid_style`
- `_grid_color_count`
- `_grid_items`
- `_grid_common_css`

Production owners:

- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`;
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_style.spl`;
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_declarations.spl`;
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_layout.spl`;
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_layout.spl`;
- `src/os/compositor/compositor_engine2d.spl`.

Frozen grid fixture:

- viewport 32×24; grid width 18;
- columns 6 and 10 with 2 gap; rows 5 and 7 with 2 gap;
- command geometry: grid `[0,0,18,20]`, A `[0,0,6,5]`,
  B `[8,0,10,5]`, C span `[0,7,18,7]`, D implicit `[8,16,10,4]`;
- exact Engine2D areas: red 30, green 50, blue 126, magenta 40.

Frozen block control:

- control `[0,0,18,21]`;
- children `[0,0,18,5]`, `[0,5,18,5]`, `[0,10,18,7]`,
  `[0,17,18,4]`;
- exact areas 90, 90, 126, and 72.

Current expected result: the bounded declaration/layout implementation,
executable source, truthful pinned manifest, and canonical manual landed in
`b17e868199af` and passed independent static review. The manifest remains
`red-not-run`, qualified execution is still blocked, and no complete CSS Grid
or full CSS support claim is made.

### CSS/JavaScript animation Draw IR trace

Existing source:

`test/02_integration/rendering/browser_session_script_css_animation_spec.spl`

Scenario:

- `should trace JavaScript pause and resume through deterministic Draw IR frames`

Frozen displayed step:

- `Trace CSS animation through deterministic Draw IR frames`

The scenario uses BrowserSession's monotonic clock and JavaScript DOM bridge,
then lowers the selected animation instances into the canonical
`DrawIrComposition`. Initial red, an interpolated frame, paused/resumed color
holds, and the forwards-filled blue completion each require the exact 32×24
Draw IR command and 768 matching Engine2D pixels with no skipped commands.

Current expected result: executable source and the canonical generated manual
are complete with zero stubs. Qualified runtime evidence remains blocked
because the available pure-Simple Stage2 compiler fails discovery on the
pre-existing `src/lib/gc_async_mut/web/browser_session.spl:1287` parse error;
no bootstrap or Rust-seed fallback is permitted.

### Generated-GUI combination gate

Existing source:

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_generated_html_css_combinations_spec.spl`

The first scenario freezes semantic panel HTML with flex, padding, border, and
text styles. The lane must add producer identity and canonical
semantic/layout/DrawIR/Engine2D assertions rather than treating its current
pixel helper or property-name occurrence as traceability. All 38 scenarios map
to canonical manual scenarios and qualified execution receipts before AC-3 can
pass.

## Executable SSpec lanes

### Traceability truth gate

Update the checker and its system SSpec so PASS requires:

- the plan exists;
- every matrix row maps to an executable scenario and canonical manual;
- current source/manual hashes align;
- changed specs report zero stubs;
- executed/pass/fail counts and qualified binary SHA are present;
- applicable semantic/layout/DrawIR/Engine2D oracles are declared;
- unsupported rows have executable fail-closed/ignored behavior.

The checker must not read its own inventory spec or this plan as proof that a
name has executable behavior.

### HTML grouped behavior

Add canonical specs under:

`test/03_system/feature/web_platform/html/`

Disjoint groups:

1. document metadata/inert/resource fallback;
2. sectioning/grouping/text/ruby/edit/list/table;
3. forms and interactive elements;
4. embedded/media fail-closed behavior;
5. UA default display and geometry.

Each visible group proves semantic identity, stable parentage, layout geometry,
DrawIR commands/style/clip, and exact Engine2D pixels. Hidden/inert groups prove
absence from layout/DrawIR/pixels. Fixtures must not force `display` or geometry
that masks UA-default bugs.

### Implemented CSS behavior

Reclassify every one of the 284 names from source and executable behavior,
never from the inventory literal.

Highest RED groups:

1. unrecognized claimed properties, including grid/table/list/multicol/blend;
2. invalid declaration and CSS-wide cascade winner semantics;
3. metadata-only properties without layout/raster consumers;
4. transition/animation/transform/flex/alignment/logical longhands with no
   authored declaration coverage;
5. isolated baseline-vs-property DrawIR/Engine2D evidence replacing coincidental
   grouped pixels.

The active `scrollbar-width`/CSS-wide cascade patch is quarantined and must not
be mixed into new parallel edits.

### Unsupported CSS behavior

Production order:

1. grid foundation;
2. scroll margin/padding/snap and anchoring;
3. fragmentation/multicol and page-break aliases;
4. border-image;
5. counters;
6. shapes;
7. motion path;
8. typography/layout: `hanging-punctuation`, `hyphenate-character`,
   `text-box`, `text-box-edge`, `text-box-trim`.

Masking/compositing/filtering, perspective, arbitrary image orientation, and
view transitions remain unsupported until the canonical shared DrawIR and
Engine2D capability exists. Computed-style-only tests cannot promote them.

Speech/aural properties remain explicit nonvisual/TTS exclusions.

Exact primary owners are the canonical renderer declaration/style, layout, and
paint-layout modules, `simple_web_render_session.spl` for retained scroll or
animation state, the hosted renderer worker for queued browser input, and the
existing Engine2D compositor used by Web-platform SSpecs. Each RED spec freezes
numeric fixture geometry and pixel/color controls before source implementation.

## RenderDoc acceptance scope

This plan owns state AC-1, AC-2, and AC-3: HTML/CSS traceability and generated
combination behavior.

AC-4 through AC-7 remain governed by:

- `doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md`
- `doc/07_guide/app/ui/gui_web_2d_vulkan_setup.md`
- `scripts/check/check-gui-renderdoc-feature-coverage-status.shs`
- `test/03_system/check/gui_renderdoc_feature_coverage_status_spec.spl`

The aggregate feature cannot complete until both this plan and those
Vulkan/RenderDoc gates pass.

## Manual policy

- Executable `.spl` remains under `test/`; none under `doc/06_spec`.
- Regenerate only canonical mirrors after changed specs settle.
- Delete stale duplicate mirrors under `doc/06_spec/test/...` only after the
  canonical manual is generated and independently reviewed.
- Primary behavior steps remain visible; setup/checkers may be folded only when
  complete executable source remains available.
- Manuals retain scope and claim-boundary prose, requirement/plan/design links,
  source hash, runner evidence, and zero-stub status.

## Execution constraints

Do not use unqualified `bin/simple`, the Rust seed, or full bootstrap. Current
stage-2 is admitted for native-build only. Until a qualified target binary can
execute the specs, status remains evidence-blocked and no executable PASS is
claimed. The current concrete blocker is the deployed pure-Simple wrapper
failing its bounded test-ABI admission probe; the one direct artifact attempt
segfaulted and must not be promoted to evidence or repeated in this tranche.

## Pass criteria

- no inventory-only PASS rows;
- every claimed row has an executable scenario and current manual;
- all applicable canonical-oracle columns are proven;
- all selected scenarios execute and pass on a qualified binary;
- unsupported rows remain explicit;
- source/manual/report counts and hashes agree;
- `find doc/06_spec -name '*_spec.spl'` returns zero;
- independent highest-capability review returns PASS.

## Generator/WebIR audit gaps

These rows are additive backlog. They do not change any earlier RED, FAIL, or
evidence-blocked classification. Here WebIR means the existing Web
semantic/layout layer, not a second drawing IR.

| Work row | Audit gap | Required evidence | Status |
|---|---|---|---|
| GEN-WEB-001 generator provenance | `simple_web_generated_html_css_combinations_spec.spl` embeds generated cases without stable generator/schema identity, input hashes, or case IDs | Emit and assert generator identity, schema version, input hashes, and unique case IDs in the executable spec and canonical manual | RED |
| GEN-WEB-002 fail-closed merge | The manifest/report join lacks executable negative coverage for duplicate IDs, missing records, stale source/manual hashes, and unknown statuses | Add fail-closed scenarios to `html_css_rendering_manifest_traceability_spec.spl` for every rejected merge condition | RED |
| GEN-WEB-003 retained manifest | The 38 generated scenarios, 50 fixture cases, and element/property rows are not joined by one retained per-case manifest with qualified execution receipts | Retain a versioned manifest that maps each case to requirements, source/manual hashes, oracle class, runner SHA, and result | RED |
| GEN-WEB-004 canonical WebIR ownership | Generated-combination pixels do not alone prove the canonical Web semantic/style/layout to `DrawIrComposition` to Engine2D route | Add producer identity, semantic/style/layout, exact Draw IR, discriminating pixel, and negative-control assertions without adding a parallel WebIR | RED |
| GEN-WEB-005 canonical manuals | The canonical generated-combinations manual is stale and a duplicate legacy mirror remains under `doc/06_spec/test/` | Regenerate the canonical manual only after executable rows settle; prove current source hash and zero stubs before deleting the duplicate mirror | RED |

## Batch 22/23 bounded traceability addendum (2026-07-31)

These rows are additive bounded evidence and do not change any HTML/CSS
inventory count or prior RED/FAIL classification.

| REQ/NFR | Row/group | Support | Executable spec/scenario | Production owners | Required oracle | Manual/result | Status |
|---|---|---|---|---|---|---|---|
| REQ-003/004/021 | CSS flex column-gap wrapping | Bounded behavior landed in `d620217fb0c` | `test/02_integration/rendering/simple_web_layout_child_index_spec.spl`: exact three-item row/column-gap wrapping | canonical flex layout, Draw IR, Engine2D | wrap threshold includes column gap; exact item rectangles, Draw IR, and discriminating pixels | current mirror; qualified execution/docgen unavailable | Evidence-blocked |
| REQ-003/004/005/006/007/017/021 | Finite animation terminal cache | Bounded behavior landed in `1671c187b9f` | `test/01_unit/os/compositor/simple_web_window_renderer_spec.spl`: finite midpoint/terminal retention, reuse after damage, and timed/static negative controls | Web render-session cache, canonical Draw IR renderer, Engine2D pixel backend | exact terminal artifact identity and pixels; no untimed/timed cross-admission; stable reuse after unrelated damage | current mirror; qualified execution/docgen/performance unavailable | Evidence-blocked |

The existing animation trace row remains evidence-blocked; this addendum
extends it only with finite terminal artifact retention and reuse. The iframe
row remains RED: current Draw IR embedding design leaves child script sharing,
navigation, and input unsupported and defines no sandbox-origin or
broker-capability contract. Animation lifecycle candidate `47df593f600` is
REJECTED and not in `origin/main`; none of its traceability edits are admitted.

## Batch 24/25 bounded traceability addendum (2026-07-31)

These rows are additive evidence only and do not change HTML/CSS inventory
counts or prior RED/FAIL classifications.

| REQ/NFR | Row/group | Support | Executable spec/scenario | Production owners | Required oracle | Manual/result | Status |
|---|---|---|---|---|---|---|---|
| REQ-003/004/019/021 | CSS collapsed-border width precedence | Bounded repair landed in `d01ff82c92a` | `test/03_system/feature/web_platform/css/table_formatting_spec.spl`: wider-vs-stronger-style and equal-width style controls | canonical table layout and Draw IR/Engine2D paint | width wins before style; exact edge commands and discriminating pixels | canonical manual current; qualified execution unavailable | Evidence-blocked |
| REQ-004/019/021 / NFR-004 | Resolved image opacity cache | Bounded shared-resource repair landed in `7fa1a11ff3c` | `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl` plus `test/03_system/os/simpleos_host_gpu_image_execution_contract_spec.spl` | shared Draw IR image resolver and Engine2D backend | opaque/translucent classification, repeated blend pixel parity, malformed resource rejection, fresh-device preflight | canonical manuals current; no qualified numeric runtime evidence | Evidence-blocked |
| REQ-003/004/019/021 | CSS viewport-fixed positioning | No accepted implementation; replacement lane active and uncommitted | future canonical layout/Draw IR/Engine2D scenario after style-owner repair | shared style, block/flex/grid/table layout dispatch, paint/hit partition | viewport anchoring under scroll, transformed ancestor behavior, auto/zero z-order distinction, exact pixels/hits | predecessor `98ec2f997eb` rejected | RED |

Animation lifecycle remains RED: candidate `47df593f600` is rejected for stale
path identity, scalar list handling, time precision, unbounded lazy tasks, and
missing cancel/restart/detach controls. Iframe is DESIGN-GO only and
implementation RED until a broker-owned frame identity/origin/capability ledger
precedes child runtime work. No runtime, docgen, numeric performance, aggregate
HTML/CSS, or goal PASS is admitted.

## Reviewed bounded reconciliation (2026-07-31)

This matrix extension preserves every prior RED/FAIL row and execution boundary.

| REQ/NFR | Row/group | Support | Executable spec/scenario | Production owners | Required oracle | Manual/result | Status |
|---|---|---|---|---|---|---|---|
| REQ-003/004/021 | CSS gap declaration winners | `be08f84be5c` + `1d16db5e149` + `dc55d6dffde` + `ca91c19d7f8` | `flex_gap_zero_cascade_spec.spl`: supported `N`/`Npx`, duplicate, `initial`, `unset`, and default-parent-inherit controls | canonical declaration dispatch/full owners, Style, Web layout, DrawIR, Engine2D | valid winner survives malformed duplicates; exact zero/reset geometry and pixels | reviewed manual; execution/docgen unavailable | STATIC REVIEW PASS; nonzero `inherit` and `revert-layer` RED |
| REQ-003/004/005/006/007/017/021 | Layout keyframe admission | `f57d9bc4600` + `782477146a9` | hosted worker animation controls for unused layout keys and empty final keyframes | canonical HTML layout renderer, render session, DrawIR, Engine2D | unused keys do not invalidate layout; a final empty keyframe shadows earlier duplicates | reviewed manuals; qualified execution unavailable | STATIC REVIEW PASS / PERF-EVIDENCE-HELD; lifecycle and multi-list RED |
