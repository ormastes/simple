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

Batch-2 functional evidence now mirrors the exact system-test matrix:
document/title/style/navigation rebuild all stages; viewport retains parse;
active animation retains parse/CSS/base style; image, scroll, and caret retain
parse/CSS/style/raw layout and repaint only; unchanged frames increment reuse
only. Composition revisions increment on every dirty paint. Canonical Draw IR
checksums change only when Draw IR changes, so title-only and out-of-band image
pixel replacement deliberately retain the prior checksum. Four same-shape
navigation replacements must keep retained node/style/box/command counts
constant, and close must zero them.

| Functional change | serialize | parse | CSS | style | layout | paint | composition |
|---|---:|---:|---:|---:|---:|---:|---|
| unchanged | +0 | +0 | +0 | +0 | +0 | +0 | revision/checksum stable; reuse +1 |
| title or DOM | +1 | +1 | +1 | +1 | +1 | +1 | revision +1; checksum changes only for painted DOM |
| stylesheet or navigation | +1 | +1 | +1 | +1 | +1 | +1 | revision +1 |
| image pixels | +0 | +0 | +0 | +0 | +0 | +1 | revision +1; Draw IR checksum stable |
| viewport | +0 | +0 | +1 | +1 | +1 | +1 | revision +1 |
| active animation | +0 | +0 | +0 | +1 | +1 | +1 | revision/checksum +1/change |
| scroll or caret | +0 | +0 | +0 | +0 | +0 | +1 | revision/checksum +1/change |
| close | — | — | — | — | — | — | retained counts zero |

This closes the source-level functional plan only. The performance lane remains
fail-fast until a healthy production artifact supplies changed/unchanged
latency, allocation, RSS, and 10,000-cycle receipts. Do not label the counter
matrix as NFR-WEB-BROWSER-003 evidence.
Checksum evidence is explicitly on demand: dirty rendering invalidates the
cached digest, unchanged reuse preserves it, and only test/report code calls
the lazy checksum accessor. Draw IR serialization and SHA-256 are forbidden in
the production frame hot path merely to maintain counters.

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

## Remaining-production tranche (2026-07-29)

Three guided sidecars completed disjoint TDD lanes under the frozen owners:

1. broker HSTS provenance in `HostedBrowserRendererProcess`;
2. SimpleScript navigation/close reclamation in `SimpleScriptExecutor`;
3. empty atomic inline baseline layout in the canonical HTML line formatter.

Root Codex is merge owner and generated-manual reviewer.
`browser_surface_adversary` and `ordered_meta_csp` performed the final
high-capability read-only review; both returned PASS after two repair cycles.
The live HTTPS/certificate row, native timing/RSS/GC rows, and the unadmitted
hosted-WM runtime-provider receipt remain explicit blockers, not exclusions.

## Draw-IR and CSS follow-up tranche (2026-07-29)

- `drawir_webir_refactor`: removed quadratic visible-material witness text
  copying in the existing HTML-layout owner; no WebIR type was added.
- `css_multiple_backgrounds`: added the bounded two-URL shared-longhand profile
  through BrowserSession admission, Style, Draw IR, and Engine2D.
- `runtime_provider_admission`: hardened explicit DSO admission and fd-bound
  launch; trusted production build provenance remains RED after the
  three-cycle cap.
- Root Codex remains merge/manual owner. `browser_surface_adversary` returned
  PASS for the rendering lanes; runtime-provider production admission remains
  FAIL and is not promoted.

## Measured GPU paint follow-up (2026-07-29)

- The presenter path now calibrates paired upload/GPU routes with exact pixels
  and device provenance; invalid evidence returns the CPU oracle.
- TODO: move calibration off the first production frame and into renderer-owned
  state before enabling it by default for dynamic layouts.
- TODO: apply the measured policy to the generic
  `simple_web_layout_engine2d_fast` path, then retain end-to-end timing,
  readback, and fallback evidence for that primary route.

## Ten-lane recovery and conformance batch (2026-07-30)

The environment permits six sidecars plus the merge owner, so these ten lanes
run in two batches. Every lane is bounded to one worktree, one owner, and at
most three verify/fix cycles. No lane may use the Rust seed as its checker,
deploy an unqualified binary, or merge static-only evidence.

| Lane | Owner | Scope | Acceptance / dependency | Status |
|---|---|---|---|---|
| 1 | `stage23_cranelift_recovery` | Recover an isolated pure-Simple Stage2/3 checker with the supported dynload wrapper and Cranelift | Stage2/3 provenance and sanity PASS; no Stage4/5 or deploy | READY; execution deferred by three-cycle cap |
| 2 | `pending_classifier_validation` | Validate the canonical terminal-`pending(...)` parser fix and regenerated manual | Focused source check and unit/system SSpecs pass with Lane 1 artifact | READINESS PASS; blocked on 1 |
| 3 | `grid_gap_alias_validation` | Validate `grid-gap`, `grid-row-gap`, and `grid-column-gap` canonical lowering | Changed-source checks plus new and unchanged-control SSpecs pass | READINESS PASS; blocked on 1 |
| 4 | `drawir_affine_validation` | Validate held Draw IR affine embedding, transport, Engine2D lowering, and four manuals | Source/spec/native checks plus route-key budget and explicit schema/legacy-hosted fixture policy | BLOCKED on 1 and schema policy |
| 5 | `js_lexical_parent_validation` | Validate the held JavaScript lexical-parent collector and full 1,000-dispatch scenario | Focused check and collector SSpecs pass; no fake manual steps | READINESS PASS; blocked on 1 and 2 |
| 6 | `content_visibility_gpu_paint` | TDD the GPU container-paint/descendant-suppression mismatch without editing an owned dirty renderer | RED CPU/DrawIR/GPU parity spec; implementation waits for owner handoff | RED patch ready; owner blocked |
| 7 | `css_transform_drawir_producer` | Lower CSS transforms through Web semantic/layout into canonical Draw IR affine data | Zero relayout, exact sampled/sibling pixels, ordered nested batches, strict multi-batch protocol, native/JIT proof | BLOCKED on 4, 6, and owner handoff |
| 8 | `html_css_traceability` | Reconcile `html_css_spec_traceability.md` against executable modern SSpecs/manuals | Preserve every origin RED row; append generator/WebIR work without destructive replacement | AUDIT COMPLETE; repair blocked on dirty owner |
| 9 | `browser_perf_memory` | Profile retained rendering, animation, close/replacement roots, latency, and max RSS | Real child-process receipts and 10k plateau; stage O(N²) ancestor walks/serialization first | AUDIT COMPLETE; harness blocked on 1 |
| 10 | `live_css_animation_evidence` | Run existing CSS+rAF+Engine2D pixel and external bitmap evidence | Animation spec plus image-taskbar exact-ARGB Electron wrapper PASS | PREFLIGHT PASS; blocked on 1 and merged 2–7 |

Merge order is 2, 3, 4, 5, 6, 7, then evidence lanes 8–10. Root Codex is
merge owner and final reviewer. Lanes with file overlap return patches instead
of rebasing or editing shared owners.

The working replacement of `html_css_spec_traceability.md` is rejected because
it deletes the authoritative RED/FAIL matrix. Restore the origin matrix before
adding generator metadata, fail-closed merge tests, manifests, explicit WebIR
ownership, or regenerated manuals.

## Ten-lane implementation-preparation batch (2026-07-30)

These lanes run in two scheduler batches and return isolated patches. A RED
spec may be preserved but not pushed as green evidence. Production files with
an active owner remain patch-only until merge-owner handoff.

| Lane | Owner | Scope | Acceptance / dependency | Initial status |
|---|---|---|---|---|
| 11 | `affine_schema_policy` | Decide Draw IR affine wire compatibility | Explicit schema/version policy and hostile legacy/current fixtures | READY |
| 12 | `affine_legacy_fixture` | Add legacy hosted payload compatibility RED coverage | Identity defaults or explicit version rejection; no ambiguous v2 decode | BLOCKED on 11 |
| 13 | `multibatch_protocol_security` | Specify hostile multi-batch browser protocol validation | Root ownership, unique IDs, aggregate budgets, affine/singular/overflow rejection | READY |
| 14 | `content_visibility_gpu_fix` | Repair the two GPU visibility predicates behind Lane 6 RED | Canonical ancestor-only semantics; no parallel renderer owner | PATCH-ONLY; owner handoff required |
| 15 | `traceability_additive_repair` | Preserve origin RED matrix and append generator/WebIR work | Zero deleted authoritative rows; every new claim names evidence or stays RED | READY |
| 16 | `spec_to_sspec_fail_closed` | Harden generator metadata and generated-region merge | Required tags, exact outside-byte preservation, duplicate/malformed rejection, idempotence | READY |
| 17 | `spec_to_sspec_integration_manifest` | Design update-mode integration and HTML/CSS manifest evidence | Executable integration SSpec, generated manual path, drift/support manifests | BLOCKED on 16 |
| 18 | `browser_budget_harness` | Replace perf placeholder with a realistic lifecycle RED harness | Child PID timing/RSS, warm samples, 10k plateau, close/replacement receipts | BLOCKED on checker |
| 19 | `paint_ancestor_complexity` | Bound repeated ancestor walks before adding a cache | Depth fixture and stage timing first; root-cause-only optimization | READY |
| 20 | `electron_exact_argb_gate` | Keep one exact external CSS/animation bitmap gate current | No silent fallback, exact proof paths/checksums, obsolete wrapper retired or repaired | BLOCKED on checker/runtime |

Merge order is 11, 12, 13, 14, 15, 16, 17, then evidence lanes 18–20.
Lanes 12–14 must be reviewed together before affine or transform production
work proceeds.
