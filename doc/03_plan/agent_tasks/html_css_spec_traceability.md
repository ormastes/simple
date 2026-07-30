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

## Completed audit and bounded implementation lanes

| Lane | Result |
|---|---|
| HTML element traceability | RED: 12 Full, 73 Partial remaining, 7 bounded selected-profile rows (`hr`,`fieldset`,`legend`,`dl`,`dt`,`dd`,`article`), 11 unsupported, 2 inventory-only, 8 checker omissions; no double-count |
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
