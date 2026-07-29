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

Current bounded HTML slice: plain `hidden` is a lowest-priority presentational
default shared by software paint and Draw IR. Author CSS may override it.
`hidden="until-found"` remains assigned to future find-in-page/`beforematch`
work and is not counted as supported.

Retained-render delivery is serialized into bounded sub-batches so agents do
not collide in the worker or renderer:

1. **TDD/revisions:** edit the existing BrowserSession and worker SSpecs first;
   assert real stage counters for unchanged/mutation/navigation/style/resource
   transitions. Then repair `ui_access_revision` as the document revision and
   add only style/resource revisions plus `BrowserRenderSnapshot`.
2. **Canonical renderer session:** own
   `simple_web_html_layout_renderer.spl` and its existing private stage files;
   add `SimpleWebRenderSession` around the current stage values. Do not add
   WebIR, Draw-IR diffing, or a pixel cache.
3. **Worker integration:** own
   `hosted_browser_renderer_worker.spl`; replace `_worker_frame`'s full rebuild,
   add reset/close release, and expose counters to focused tests/evidence.

Each sub-batch returns to the merge owner before the next begins. The HTML/CSS
fidelity agent may change the same renderer files, so it must finish before
sub-batch 2 starts.

Status (2026-07-29): the merge owner authorized the smallest exact first
slice. Source now has conditional BrowserSession snapshots, one worker-owned
`SimpleWebRenderSession`, unchanged-frame reuse counters, and close
reclamation. It retains the existing combined semantic/layout/Draw IR result;
stage-selective mutation, navigation, stylesheet/resource, viewport,
animation, scroll/overlay, and soak rows remain separate RED follow-ups.
Runtime execution is blocked by the unhealthy deployed pure-Simple target.

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
- external PNG lane: one sidecar each for strict bounded PNG decode, additive
  `SBRF5` image-resource transport, BrowserSession/CSP/HSTS request ownership,
  canonical layout/Draw IR image emission, and absolute pixel evidence; merge
  owner and final reviewer are highest-capability Codex;
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

The retained-render counter matrix is the first evidence gate:

- unchanged monotonic advance: only `reuse_count`;
- CSS animation: style/layout/paint, not parse/CSS;
- scroll/caret overlay: paint, not parse/CSS/style/layout;
- DOM/title/style/navigation: exact conservative invalidation;
- decoded image replacement: paint only;
- 10,000 replacement/close loop: one retained stage set plateaus and all
  retained counts reach zero after close.

Production latency/RSS rows remain blocked until the healthy pure-Simple
Phase 2/3 target can execute; source counters never turn those rows green.

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
