# HTML/CSS SSpec Traceability Agent Tasks

Merge owner: root Codex agent

Final reviewer: independent highest-capability agent

Canonical plan:

`doc/03_plan/sys_test/html_css_spec_traceability.md`

## Frozen steps

- `Verify executable HTML and CSS traceability`
- `Trace HTML elements through Web semantics and Draw IR`
- `Trace implemented CSS properties through canonical rendering`
- `Classify unsupported CSS properties without false implementation claims`

Fieldset/legend bounded lane:

- `Parse fieldset and legend as a semantic parent-child pair`
- `Apply selected user-agent defaults before authored CSS`
- `Lower authored fieldset and legend boxes to exact Draw IR geometry`
- `Rasterize exact component pixels against an unstyled control`

Definition-list bounded lane:

- `Parse omitted dt and dd end tags as definition-list siblings`
- `Apply definition-list user-agent defaults before authored CSS`
- `Lower authored definition-list boxes to exact Draw IR geometry`
- `Rasterize exact definition-list pixels against a plain control`

Small-element bounded lane:

- `Parse small as an inline body child`
- `Apply the small user-agent font size`
- `Lower small text to exact Draw IR geometry`
- `Rasterize absolute small-element pixels`

Frozen helpers:

- `_small_node_index`
- `_small_command`
- `_small_text_command`
- `_small_style`
- `_small_geometry`

## Completed audit and bounded implementation lanes

| Lane | Result |
|---|---|
| HTML element traceability | RED: 12 Full, 64 Partial remaining, 16 bounded selected-profile rows (`hr`,`fieldset`,`legend`,`dl`,`dt`,`dd`,`article`,`blockquote`,`header`,`details`,`summary`,`figure`,`menu`,`small`,`abbr`,`time`), 11 unsupported, 2 inventory-only, 8 checker omissions; no double-count |
| Implemented CSS traceability | RED: self-satisfying 284 count, unrecognized and metadata-only claims |
| Unsupported CSS classification | 92 production, 23 speech/aural, 1 deprecated, 1 false scrape |
| SSpec/manual quality | FAIL: missing plan/REQs, stale manuals/counts, no executed evidence |
| Closed checker | Landed in `fc73115d0214`; behavioral counts remain zero without independent admission |
| Inert/media/form/caption/animation | Bounded source/spec/manual work landed; qualified execution and corpus accounting remain open |
| Iframe | Design landed in `771dfb23835b`; TDD regeneration and implementation remain open |
| HTML `hr` | Current bounded lane: native UA defaults plus exact `0`/`0px`/`none`/`hidden` and mixed-invalid/missing border cascade controls through semantic Web layout, DrawIR, and exact Engine2D pixels; qualified execution remains open |
| Fieldset/legend selected profile | Current bounded lane: canonical UA defaults, four-side authored border clearing, semantic/style/exact DrawIR/pixel SSpec, and handwritten draft mirror; special legend formatting/cutout, disabled propagation, admitted docgen, and qualified execution remain open |
| Definition-list selected profile | Current bounded lane: cross-kind omitted-end-tag repair, canonical `dl`/`dt`/`dd` UA defaults and authored overrides, semantic/style/exact DrawIR/pixel SSpec, and handwritten draft mirror; admitted docgen, qualified execution, and corpus accounting remain open |
| Parallel HTML/CSS/animation cycle | Landed in `fb4050c3d2b`: `article`, width/height-led `aspect-ratio`, CPU outline paint, real SimpleScript/CSS DrawIR frames, completed-animation reuse, and identity-matched font metadata; all remain evidence-blocked pending qualified pure-Simple execution/docgen |
| Animation resource boundary | Landed in `d4ffb28dae4`: the canonical event-loop owner caps both timers and `requestAnimationFrame` at 256 tasks, rejects overflow, and resumes animation after drain; modern SSpec/manual are present and qualified execution/docgen remain held |
| Scripted body animation reconciliation | Landed in `0d6c055a489`: changed SimpleScript body assignments preserve the single DOM revision owner, reconcile animation instances, and advance timer-driven DrawIR/hit frames; unchanged assignments remain no-ops and qualified execution/docgen remain held |
| HTML `blockquote` selected profile | Landed in `8f2ae532371`: canonical semantic parentage and UA block margins lower through Web layout to exact DrawIR geometry and Engine2D pixels; complete mirrored manual present, qualified execution/docgen remain held |
| HTML `header` selected profile | Landed in `9f720c62c72`: canonical semantic parentage and UA block behavior lower through Web layout to exact DrawIR geometry and Engine2D pixels; complete mirrored manual present, qualified execution/docgen remain held |
| HTML `figure` selected profile | Landed in `897368fb592`: selected UA margins lower through canonical Web layout to exact DrawIR geometry and Engine2D pixels; static evidence is held and qualified execution/docgen remain unavailable |
| HTML `menu` selected profile | Landed in `b107a4e2a9e`: selected LTR UA list spacing lowers through canonical Web layout to exact DrawIR geometry and Engine2D pixels; static evidence is held and qualified execution/docgen remain unavailable |
| HTML `small` selected profile | Landed in `b9e1a0e6707`: selected medium-UA `smaller` maps inherited 16 px text to 13 px through semantic style, baseline layout, DrawIR text, and absolute Engine2D pixel discriminators; static evidence is held and qualified execution/docgen remain unavailable |
| HTML `abbr` selected profile | Landed in `8beb64585b2`: native `<abbr>` remains in inline flow with exact semantic/style/layout/DrawIR/pixel controls; static evidence is held and qualified execution/docgen remain unavailable |
| HTML `time` selected profile | Landed in `7b290473ae6`: native `<time>` matches `<span>` inline geometry, DrawIR text advances, and pixels while a forced block remains the negative control; static evidence is held and qualified execution/docgen remain unavailable |
| CSS `text-transform` DrawIR parity | Landed in `e7af94e921c`: the canonical DrawIR text owner applies the computed transform and existing RTL reversal before metrics and every fallback/shaped/resolved text command; literal-uppercase command geometry/font payload and full CPU-DrawIR pixels are the exact control; static evidence is held |
| CSS implicit keyframe endpoints | Landed in `0e4b75b167b`: omitted per-property endpoints synthesize the underlying value, incompatible values interpolate discretely, and the four-step scenario traces exact scheduler, DrawIR, and Engine2D results; static evidence is held and qualified execution/docgen remain unavailable |
| CSS logical sizing and writing mode | Landed in `08de37b0902`: logical size/min/max declarations map through final horizontal, vertical, and sideways writing-mode winners with authored-order, DrawIR, and Engine2D pixel controls; static evidence is held and qualified execution/docgen remain unavailable |
| Padding cascade order | Landed in `9f720c62c72`: one linear declaration-family resolver preserves authored shorthand, physical, and horizontal-LTR logical order while ignoring malformed values; exact semantic-to-pixel evidence present |
| Fractional opacity siblings | Landed in `9f720c62c72`: same-size clipped sibling roots use viewport-area-bounded cropped Draw IR batches; backdrop and differing-size cases fail closed, preserving the single Engine2D offscreen pool |
| Signed animation time and script epoch | Landed in `9f720c62c72`: negative second/millisecond parsing reaches exact consecutive frames, and unrelated SimpleScript stylesheet replacement preserves an unchanged animation signature |

## Safe parallel implementation lanes

1. Checker/report lane
   - owns traceability scripts, checker specs, report schema, and plan links;
   - does not touch renderer source or behavior specs.

2. HTML RED SSpec lane
   - owns new files under `test/03_system/feature/web_platform/html/`;
   - no renderer edits until RED rows are independently reviewed.

3. CSS RED SSpec lane
   - owns new isolated specs under
     `test/03_system/feature/web_platform/css/`;
   - excludes current `scrollbar_wpt_spec.spl` and quarantined renderer files.

4. Manual lane
   - runs qualified pure-Simple docgen only after specs settle;
   - owns canonical mirrored manuals and stale-duplicate deletion;
   - cannot declare executable PASS.

Current next lanes are the independently admitted runner/manual workflow,
fresh bounded iframe TDD regeneration, and per-row corpus accounting. Do not
reopen landed bounded behavior unless its focused evidence regresses.

## Batch 22/23 bounded rendering addendum (2026-07-31)

| Lane | Result | Status |
|---|---|---|
| CSS flex column-gap wrap | Landed in `d620217fb0c`: row wrapping counts column gap before admitting the next item and traces exact rectangles through canonical Draw IR and Engine2D pixels. | STATIC/EVIDENCE-HELD; qualified execution/docgen unavailable |
| Finite animation terminal cache | Landed in `1671c187b9f`: terminal animation artifacts remain timed and reusable while untimed static entries cannot satisfy terminal requests. | STATIC/EVIDENCE-HELD; qualified execution/docgen/performance unavailable |

These bounded rows do not change HTML/CSS inventory counts. Iframe work must
first define the child sandbox-origin and broker-capability contract; the
current Draw IR embedding design explicitly leaves child script sharing,
navigation, and input unsupported. That architecture lane remains RED before
fresh TDD or implementation.

## Batch 24/25 bounded rendering addendum (2026-07-31)

| Lane | Result | Status |
|---|---|---|
| Collapsed table border precedence | Landed in `d01ff82c92a`: competing collapsed borders prefer width before style and retain exact canonical Draw IR/Engine2D controls. | STATIC/EVIDENCE-HELD; qualified execution unavailable |
| Resolved image opacity cache | Landed in `7fa1a11ff3c`: the shared Engine2D resource caches one bounded opaque/translucent classification while preserving repeated blend pixels and rejecting malformed data. | STATIC/PERF-EVIDENCE-HELD; no numeric runtime claim |
| Viewport-fixed positioning | The replacement lane is ACTIVE/UNCOMMITTED; predecessor `98ec2f997eb` is rejected because style ownership, layout dispatch, paint partitioning, and `z-index:auto` semantics are unsound. | RED; no accepted implementation or execution |

Animation lifecycle candidate `47df593f600` remains REJECTED/DO-NOT-MERGE:
path-only target identity, scalar animation state, lossy millisecond
arithmetic, unbounded stale tasks, and missing cancellation/restart/detachment
coverage require a new design after the atomic DOM-route dependency. Iframe is
DESIGN-GO only and implementation RED until the broker owns frame identity,
origin, and capability state. These rows do not change inventory counts or
admit runtime, docgen, performance, aggregate HTML/CSS, or goal PASS.

## Serialized source lanes

Renderer source changes are serialized because declaration/style/layout/paint
owners overlap the quarantined CSS-wide cascade patch.

Order:

1. shared valid-declaration/CSS-wide cascade owner;
2. HTML UA defaults;
3. grid foundation;
4. scroll snap/anchor;
5. fragmentation and border image;
6. counters/shapes/motion path;
7. typography/layout properties after their RED geometry specs;
8. remaining supported-profile reclassification.

Each source lane starts from accepted RED SSpec and receives an independent
review before merge.

## Fail-fast rule

Any newly declared scenario helper without implementation must call
`fail("REQ-WEB-BROWSER-NNN: ...")`. No `pass_todo`, empty helper, trivial
boolean assertion, inventory-string assertion, or source-grep assertion can
mark a behavior covered.

## Merge gates

- no overlap with unrelated report or quarantined CSP/CSS work;
- real `@req` tags;
- canonical matcher set;
- semantic plus applicable layout/DrawIR/Engine2D oracles;
- zero-stub generated manuals;
- qualified execution provenance;
- independent review;
- rebase/file-count safety and GitHub push.

## Reviewed bounded reconciliation (2026-07-31)

This addendum is additive: earlier inventory, RED, FAIL, and execution-held
rows remain authoritative outside the bounded cases below.

| Lane | Reviewed result | Status |
|---|---|---|
| CSS gap declaration winners | `be08f84be5c` + `1d16db5e149` + `dc55d6dffde` + `ca91c19d7f8` retain a valid `gap` winner across supported `N`/`Npx`, duplicate, `initial`, `unset`, and default-parent-inherit cases. | STATIC REVIEW PASS; nonzero `inherit` and `revert-layer` remain RED; qualified execution/docgen held |
| Layout keyframe work | `f57d9bc4600` skips unused layout keyframes and `782477146a9` preserves an empty final keyframe. | STATIC REVIEW PASS / PERF-EVIDENCE-HELD; lifecycle and multi-list behavior remain RED |

These rows do not promote aggregate HTML/CSS coverage or a production runtime
claim.
