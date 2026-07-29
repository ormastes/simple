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

## Completed audit and bounded implementation lanes

| Lane | Result |
|---|---|
| HTML element traceability | RED: 12 Full, 80 Partial, 11 unsupported, 2 inventory-only, 8 checker omissions |
| Implemented CSS traceability | RED: self-satisfying 284 count, unrecognized and metadata-only claims |
| Unsupported CSS classification | 92 production, 23 speech/aural, 1 deprecated, 1 false scrape |
| SSpec/manual quality | FAIL: missing plan/REQs, stale manuals/counts, no executed evidence |
| Closed checker | Landed in `fc73115d0214`; behavioral counts remain zero without independent admission |
| Inert/media/form/caption/animation | Bounded source/spec/manual work landed; qualified execution and corpus accounting remain open |
| Iframe | Design landed in `771dfb23835b`; TDD regeneration and implementation remain open |

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
