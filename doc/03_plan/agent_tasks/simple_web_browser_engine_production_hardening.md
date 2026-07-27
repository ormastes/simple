# Simple Web Browser Engine Production Hardening — Agent Tasks

## Coordination

- Merge owner: root Codex agent.
- Final reviewer: root normal/highest-capability Codex agent.
- Spark was requested but is not available in this environment. Normal Codex
  sidecars may perform bounded lanes; their output is not accepted without root
  review.
- Unrelated dirty work remains outside this lane.

## Frozen shared names

- `JsRuntimeProfile.Browser|Node`
- `BrowserRendererProcess`
- `BrowserDomDispatchResult`
- `SimpleWebRenderSession`
- existing `BrowserSession`
- existing `DrawIrComposition`
- existing `Engine2dCompositorBackend`

No sidecar may add a parallel browser controller, history store, DOM, event
type, parser, renderer, font path, or device owner.

## Frozen manual steps

- `Launch the production Simple browser`
- `Open the conformance page`
- `Render HTML and CSS through canonical Draw IR`
- `Run JavaScript and advance the browser clock`
- `Operate page controls`
- `Operate browser navigation controls`
- `Navigate through verified HTTPS`
- `Reject hostile origin and scheme requests`
- `Reject renderer host capability access`
- `Close the page and reclaim browser resources`
- `Measure production browser budgets`

## Frozen setup/checkers

- `_production_browser_fixture`
- `_two_origin_https_fixture`
- `_hostile_page_fixture`
- `_browser_budget_fixture`
- `_platform_evidence_row`
- `_check_canonical_draw_ir`
- `_check_dom_visible_state`
- `_check_event_phase_order`
- `_check_navigation_state`
- `_check_https_identity`
- `_check_security_denial`
- `_check_resource_reclaimed`
- `_check_budget_row`

Unimplemented helpers fail with `fail("REQ-WEB-BROWSER-NNN: ... not
implemented")`.

## Parallel lanes

### Lane A — Evidence contracts and false-green repair

Owns:

- new user-flow, security, and performance specs;
- current `browser_interaction_spec.spl` missing-artifact greenwash;
- generated manuals and traceability.

Must not implement product behavior.

### Lane B — Browser profile and navigation core

Owns:

- `browser_session*.spl`;
- URL/origin migration;
- navigation generation, stop/late-response behavior;
- browser-only JS profile selection;
- document lifecycle release.

Coordinates stable method/type changes before dependent lanes merge.

### Lane C — DOM, events, forms, and chrome

Owns:

- canonical node IDs;
- event phases/default actions/focus/text/form behavior;
- `browser_session_ui_access.spl`;
- address/reload/bookmark actions and semantic nodes.

Depends on Lane B request generation and lifecycle contracts.

### Lane D — HTML/CSS/render session and Engine2D

Owns:

- canonical production parser routing;
- `SimpleWebRenderSession`;
- stage invalidation and counters;
- Draw IR emission and persistent Engine2D submission;
- animation style integration.

Must not edit Engine3D or create a font/device path.

### Lane E — JavaScript/Simple Script clock

Owns:

- `JsRuntimeProfile`;
- Browser profile globals;
- timer/microtask/rAF clock injection;
- live DOM mutation/listener bindings;
- removal of production subprocess/fake-success paths.

Coordinates DOM bindings with Lane C and time/invalidation with Lane D.

### Lane F — Broker network, TLS, cookies, and sandbox

Owns:

- typed renderer IPC;
- broker Fetch/CORS/CSP/mixed-content/cookies/HSTS;
- platform renderer sandbox and crash containment;
- scheme/file capability policy and limits.

Platform implementation sublanes may split Linux, macOS, and Windows after the
typed IPC/policy contract is frozen.

### Lane G — GC and performance

Owns:

- memtrack/heap/RSS/frame/input instrumentation;
- lifecycle/retained-root diagnosis and fixes;
- interpreter GC root-scan regression if reproduced by browser workloads;
- 10,000-cycle soak and budget gate;
- hot-path profiling and minimum root-cause fixes.

Does not add cache layers without measured evidence.

## Batch order

1. A and B start first.
2. C, D, and E proceed after B freezes generations, profile, and document
   ownership.
3. F proceeds after typed IPC/URL origin contracts freeze.
4. G profiles the merged production path, not isolated substitutes.
5. Root merges, refactors, reviews generated manuals, and runs verification.

## Merge rules

- Each lane lists exact changed files and tests.
- Shared-file conflicts return to merge owner.
- A green supporting unit test cannot close a production acceptance row.
- Host-unavailable rows retain owner, prerequisite, exact resume command,
  artifacts, and final reviewer.
- At most three verify/fix cycles per lane; identical green commands are not
  rerun.
