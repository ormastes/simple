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
| 11 | `affine_schema_policy` | Decide Draw IR affine wire compatibility | Explicit schema/version policy and hostile legacy/current fixtures | POLICY PASS: retain v2, omit identity fields |
| 12 | `affine_legacy_fixture` | Add legacy hosted payload compatibility RED coverage | Identity defaults or explicit version rejection; no ambiguous v2 decode | STATIC REVIEW PASS; execution blocked |
| 13 | `multibatch_protocol_security` | Specify hostile multi-batch browser protocol validation | Root ownership, unique IDs, aggregate budgets, affine/singular/overflow rejection | FAIL at three-cycle cap |
| 14 | `content_visibility_gpu_fix` | Repair the two GPU visibility predicates behind Lane 6 RED | Canonical paint-ancestor semantics; no parallel renderer owner | STATIC REVIEW PASS; execution blocked |
| 15 | `traceability_additive_repair` | Preserve origin RED matrix and append generator/WebIR work | Zero deleted authoritative rows; every new claim names evidence or stays RED | PUSHED `e20ba58a3c85` |
| 16 | `spec_to_sspec_fail_closed` | Harden generator metadata and generated-region merge | Required tags, exact outside-byte preservation, duplicate/malformed rejection, idempotence | FAIL at three-cycle cap |
| 17 | `spec_to_sspec_integration_manifest` | Design update-mode integration and HTML/CSS manifest evidence | Executable integration SSpec, generated manual path, drift/support manifests | DESIGN COMPLETE; blocked on 16 |
| 18 | `browser_budget_harness` | Replace perf placeholder with a realistic lifecycle RED harness | Child PID timing/RSS, warm samples, 10k plateau, close/replacement receipts | FAIL at three-cycle cap |
| 19 | `paint_ancestor_complexity` | Bound repeated ancestor walks before adding a cache | Depth fixture and deterministic work counters first; root-cause-only optimization | FAIL at three-cycle cap |
| 20 | `electron_exact_argb_gate` | Keep one exact external CSS/animation bitmap gate current | No silent fallback, exact proof paths/checksums, obsolete wrapper retired or repaired | PUSHED `ea63b6e2ec36` |

Merge order is 11, 12, 13, 14, 15, 16, 17, then evidence lanes 18–20.
Lanes 12–14 must be reviewed together before affine or transform production
work proceeds.

Three-cycle blockers are retained, not normalized away: Lane 13 still needs a
real nonidentity child and established affine error reasons; Lane 16 still
admits tautological assertions and lacks a time import; Lane 18 must compare
10k RSS to the post-warmup baseline and narrow its NFR claims; Lane 19 must
define one render-receipt return contract and exclude checkout-only EOL churn.

## Production surface audit batch (2026-07-30)

| Surface | Current-main finding | Evidence / patch | Status |
|---|---|---|---|
| HTML/CSS rendering | Negative `z-index` parses as positive and has no negative paint bucket | Held renderer RED spec proves signed computed/Draw IR values, ordering, and three pixels | STATIC REVIEW PASS; implementation blocked |
| JavaScript animation | Production `nogc_sync_mut` JS already implements rAF/cancel/one-shot timing | Held REQ-WEB-BROWSER-006 regression adds cancellation, timestamp, DOM/style, and one-shot coverage | EXPECTED GREEN; checker blocked |
| Sandbox/network | Literal private destinations lack early broker rejection; runtime still owns post-DNS public-address enforcement | Held policy RED/patch found an IPv4-mapped IPv6 gap at final review | FAIL at three-cycle cap |
| Events/forms | Label activation does not forward default action to associated controls | Held integration RED covers explicit/nested labels, repeat order, serialization, and reopen reset | STATIC REVIEW PASS; implementation blocked |
| Navigation/chrome | Address UI retained and submitted unbounded raw input | Held UI-bound 2048-byte patch covers multibyte/pre-trim denial and state preservation | STATIC REVIEW PASS; checker blocked |
| HTTPS/TLS | Production WM runtime provider omitted Cargo `runtime-tls` | `9ada3ff6face`; TLS-enabled provider build PASS | MERGED; live certificate matrix pending |

Next merge order is address bound, label activation, negative stacking, then
their manuals. Private-egress classification must first cover IPv4-mapped IPv6
and preserve connection-time resolution enforcement. No held Simple patch is
promoted without a current pure-Simple checker.

## Held-bundle tranche (2026-07-30)

| Lane | Held worktree | Status | Resume gate |
| --- | --- | --- | --- |
| `drawir_canonical_oracle` | `/tmp/simple-drawir-canonical-oracle.VBRqIv` | static + phase-2 manual + high review PASS; unmerged | admitted current pure-Simple full CLI; run focused spec once |
| `content_visibility_gpu_guard` | current change (`simple_web_renderer_spec.spl`) | O(N) shared GPU paint state + presented-pixel parity + phase-2 manual + final high review PASS; execution HELD | admitted current pure-Simple full CLI; run focused spec once |
| `address_bound` | `/tmp/simple-address-bound.Qw0wSt/worktree` | static + phase-2 manual + high review PASS; unmerged | admitted current pure-Simple full CLI; run focused spec once |
| `eventloop_idle_drain` | `/tmp/simple-eventloop-idle-drain` | HOLD/FAIL: vacuous future timer, no performance discriminator, stale tick wording; review/docgen cap reached | redesign evidence before any executable attempt |
| `animation_csp_clock` | `/tmp/simple-animation-csp-clock` | production + spec + phase-2 manual + high review PASS; unexecuted/unmerged | admitted current pure-Simple full CLI; run focused spec once |
| `table_collapse` | current change (`table_formatting_spec.spl`) | bounded one-row/two-cell precedence + retained rerender + phase-2 manual + final high review PASS; execution HELD | admitted current pure-Simple full CLI; run focused spec once |
| `object_fit_inheritance` | `/tmp/simple-object-fit-inheritance.w2dMXw` | production + spec high review PASS; generated manual FAIL on a fifth cleanup action at the three-cycle cap | repair manual in a fresh scoped cycle before execution |
| `raf_frame_alignment` | `/tmp/simple-raf-frame-align-clean.gdkM4F` | production + spec + phase-2 manual + final high review PASS; unexecuted/unmerged | admitted current pure-Simple full CLI; run focused spec once |
| `animation_layout_classification_cache` | `/tmp/simple-animation-layout-cache.Fh8uZo` | production + spec high review PASS; phase-2 manual FAIL on a raw inline-CSS payload bullet at the regeneration cap | repair manual in a fresh scoped cycle before execution |
| `fractional_opacity_group_design` | `/tmp/simple-css-opacity-design.CqGpJo` | architecture/design/system-test proposal high review PASS; unimplemented | implement bounded Draw IR group contract, then executable evidence |

Root Codex is merge owner and final reviewer. No seed or bootstrap output may
admit or merge these patches; this tranche does not change phase or acceptance
criterion completion. No target behavior is claimed until an admitted current
pure-Simple full CLI runs the applicable focused SSpec once.

## Intensive HTML/CSS, forms, history, security, and animation batch 2 (2026-07-30)

| Lane | Held worktree / evidence | Status | Resume gate |
| --- | --- | --- | --- |
| `details_summary_rendering` | `/tmp/simple-details-summary-render` | O(N) production lowering + modern four-step SSpec + phase-2 manual + high review PASS; held and unexecuted | admitted current pure-Simple full CLI; run the focused SSpec once |
| `invalid_form_method` | `/tmp/simple-invalid-form-method.M1cWuX` | production + modern SSpec + canonical phase-2 manual + final high review PASS; held and unexecuted | admitted current pure-Simple full CLI; run the focused SSpec once |
| `maxlength_audit` | current `_browser_session_parse_maxlength` | candidate rejected: leading-digit parsing is the required non-negative-integer behavior, not a browser bug | N/A; add no workaround or bug |
| `overflow_clip_cascade` | design RED | proposed patch rejected because flattened rules lose cascade origin and `@layer` provenance | carry provenance parser -> `Rules` -> cascade owner before implementing `overflow: clip` |
| `history_parent_ledger` | `/tmp/simple-history-h1.d3de` | random-SBR2-capability-bound full ledger, off-side candidate validation, one-swap parent commit, and fail-close chrome preservation implemented statically | root final review, then run the focused SSpec once on an admitted current pure-Simple CLI |
| `primary_close_retry` | `/tmp/simple-primary-close-retry.RotRUO` | HOLD/FAIL at the three-review cap: fatal poll revokes authority inside an already-entered block, but `begin_resize` lacks a fresh authority check and may call a closed/failed renderer; other lifecycle work reviewed sound | repair the stale-authority path in a fresh scoped cycle; do not merge |
| `fractional_animation` | `/tmp/simple-animation-slice2` | HOLD/FAIL at the three-review cap: invalid longhand/shorthand tails erase the earlier valid winner (`2; -1` computes default 1 and an invalid shorthand wipes its predecessor); reconcile/apply retain unchecked timestamp subtraction | preserve last-valid declaration selection and use saturating subtraction with i64-min/boundary evidence in a fresh scoped cycle; do not merge |

Root Codex remains merge owner and final reviewer. These rows do not promote a
requirement, merge a patch, or provide executable evidence.

## Intensive HTML/CSS and animation batch 4 (2026-07-30)

| Lane | Result | Status / next gate |
| --- | --- | --- |
| `animation_microtask_pixels` | rAF schedules a Promise microtask that mutates `#stage`; `advance_time(16)` exposes the mutation before return and exact `32x24` Draw IR/Engine2D pixels change | final high review PASS; execution HELD for an admitted current pure-Simple CLI |
| `animation_production_evidence` | actual rAF timestamp `16`, stage-bound exact red-to-blue pixels, persistent Engine2D owner, and fail-closed p95/FPS/RSS/GC/10k gates | supporting evidence PASS; numeric NFR receipts remain RED |
| `content_visibility_gpu_guard` | one O(N) preorder state feeds both GPU scans; content visibility, override-visible descendants, and partial-opacity fallback match CPU-presented pixels | final high review PASS; execution HELD |
| `table_collapse` | bounded one-row/two-cell collapse retains edge styles and applies hidden/none/style/width/LTR precedence after animation in initial and retained renders | final high review PASS; execution HELD |
| `html_css_traceability` | fractional-opacity and held-border wording repaired, but `check-html-css-full-rendering-goal-status.shs` still emits inventory-derived readiness `pass` flags | FAIL/HOLD at three-cycle cap; fix the second producer before merging traceability docs |
| `bold_elements` | `<b>`/`<strong>` UA semantics are straightforward, but canonical FontRenderer rejects non-normal weight and has no face-weight/synthesis decision | FAIL/HOLD at three-cycle cap; design canonical FontRenderConfig/FontRenderer weight support first |

No batch-4 row promotes production completion. The admitted-runtime focused
SSpec run remains mandatory; bootstrap and the Rust seed are not admissible.

## Cascade-owner implementation lanes (2026-07-30)

Status: **PROPOSED / UNIMPLEMENTED**. Root Codex is merge owner and the final
normal/highest-capability reviewer. Sidecars must target these frozen names:
`CssCascadeOrigin`, `CssRuleDeclaration`, `CssRule`,
`CssCascadeDeclaration`, `CssCascadeBandRank`, `CssLayerIdentity`,
`CssLayerRegistry`,
`CssOverflowMode`, `ComputedOverflowPair`, `UsedOverflowState`, and
`cascade_provenance_overflow_clip_spec.spl`. Manual steps are `Collect
declaration provenance`, `Select cascade winners`, `Resolve CSS-wide values`,
and `Render overflow clip pixels`; checker names and the mandatory RED
`fail(...)` are frozen in the system-test plan.

| Lane | Bounded ownership | Handoff |
| --- | --- | --- |
| parser/layers | `CssRuleScan`, predeclared/reopened/nested/anonymous layer statements/paths, per-layer implicit outer sublayers, applicable document-global conditional registration, typed `Rules`, raw custom-property tokens | rebuild registry/ranks on condition-truth changes; reject element-sensitive layer order |
| cascade inputs | tag defaults, presentational hints, matched rules, element-attached inline style, important, animation candidates | every candidate carries origin/context/layer/style-rank/specificity/source/importance; unsupported user/shadow/transition inputs reject |
| winner/defaulting | precomputed band ranks, ranked selector-bucket merge, occupied-band-only sparse lower-candidate stacks, element-attached rollback, author-plus-animation `revert`, `initial`/`inherit`/`unset`/`revert-layer` | O(N), occupied bands <= matched declarations; never scan dense global layers; CSS-wide values never reach `apply_decls` |
| overflow/lowering | separate computed/used per-axis `CssOverflowMode`, cross-axis computation, root/body viewport propagation, replaced hidden→clip, padding-box/zero-margin clip edge, scroll-container/BFC/programmatic-scroll distinction, canonical Draw IR/Engine2D pixels | root/replaced boundaries remain RED until their exact matrix passes |
| selector invalidation | ancestor selectors/inheritance, descendant-to-ancestor `:has`, structural sibling/child cohorts | no whole-tree invalidation unless the dependency graph proves it necessary |
| evidence/perf | modern RED SSpec, generated manual, counters/timing/RSS fixture | no production claim before admitted pure-Simple execution |

Lower-model sidecars may inspect one bounded row only. They may not rename
shared interfaces, add a second cascade, implement paint-only `clip`, commit,
or push. Merge order is parser/layers → cascade inputs → winner/defaulting →
overflow/lowering → evidence/perf, with high-capability review after each
handoff.

## Bookmark title witness lane (IMPLEMENTED STATIC / EXECUTION HELD)

The primary design pass freezes these shared names before implementation:
`hosted_browser_title_is_valid`,
`browser_bookmark_stored_title`,
`browser_bookmark_title_or_url`,
`BrowserRendererFrameDecodeResult.document_title_present`, and the four manual
steps recorded in the system-test plan. New test helpers must be named
`setup_hosted_bookmark_title_profile`,
`check_bookmark_title_witness_admission`, and
`check_restarted_bookmark_listing`. The in-process parity helper is
`check_in_process_registry_profile_reopen` and may use only
`HostedWebContentRegistry` actions plus its parent-owned profile snapshot;
unfinished helpers must call `fail(...)`.

| Lane | Scope | Handoff |
|---|---|---|
| `bookmark_title_protocol` | Add `SBRF8`, <=684 pre-decode base64/offset/budget admission, canonical round trip, legacy policy, and hostile generation/reply/URL/title fixtures | patch only; no profile/UI edits |
| `bookmark_title_parent_profile` | Retain admitted title state, clear it on lifecycle boundaries, use empty storage sentinel and derived URL fallback in sandbox and in-process hosts | depends on protocol names |
| `bookmark_title_sspec` | Add the exact four-step persisted 512/513-byte UI scenario, sandbox listing, and public-action-only in-process registry/profile reopen parity | depends on both implementation lanes |
| `bookmark_title_final_review` | Review trust binding, schema compatibility, restart/site-swap behavior, and manual quality | normal/highest-capability reviewer |

Lower-model sidecars are **N/A** for accepting the cross-process trust decision;
they may only enumerate fixtures after the interfaces above are frozen. Root
Codex is merge owner. A separate normal/highest-capability agent is final
reviewer. No lane may commit or push independently, and no production claim is
allowed before the focused SSpec runs once on an admitted current pure-Simple
full CLI.

## Rejected and execution-held design lanes

| Lane | Exact remaining defects | Next |
| --- | --- | --- |
| hosted HTTPS | HSTS belongs to the broker, not the worker; renderer launch must unset `LD_LIBRARY_PATH` | discard the failed plan and repair both boundaries in a fresh design cycle |
| parent history | canonical `SBRHJ1` uses `O/-`, `N/-`, and `V/<canonical-base64>`; empty `V` preserves the full committed URL fragment | IMPLEMENTED STATIC / EXECUTION HELD; root merge owner and final highest-capability review required |

All other reviewed aspects are sound but unpromoted. The hosted HTTPS plan
remains rejected; parent history remains execution-held and cannot be cited as
production evidence before its focused SSpec passes.

## Held SimpleScript listener bundle

| Lane | Bundle | Status | Remaining gate |
| --- | --- | --- | --- |
| SimpleScript listeners | `/tmp/simple-simple-script-events.5IEatF` | production + modern SSpec + phase-2 manual + final high review PASS; prior vacuous system claim repaired through canonical `BrowserSession.dispatch_dom_event`, with no `inject_dom_event` path | held, unexecuted, and unmerged until an admitted current full pure-Simple CLI runs the focused SSpec once |
| primary navigation chrome cancellation | `/tmp/simple-web-pointer-safe` | fresh-cycle implementation records page-pointer ownership in `HostedBrowserRendererProcess`, emits or retains the existing pointer-up cancellation before primary chrome ownership, and adds modern SSpec wire/retry oracles | bounded static review; focused specs/docgen remain held for an admitted current pure-Simple CLI |

The held listener row covers exact UTF-8 target/event/action bounds
`2048/2049`, `64/65`, `4096/4097`; capacity `256/257`, duplicate identity and
tombstone reuse; fail-closed registration; exact listener/default ordering and
executor-root rebinding; and red-to-blue canonical Draw IR/Engine2D pixels.
Root Codex remains merge owner and final executable-evidence reviewer.

All other navigation state, paint, hit, drain, projection, partial-wire, and
lifecycle work reviewed sound but remains unpromoted.

## Renderer command capability lanes (IMPLEMENTED STATIC / EXECUTION RED)
Commit `879f28bc059` implements the atomic production SBR2 graph and its
focused modern SSpec/manual. The accepted design freezes
`BrowserRendererCommandCapability`,
`browser_renderer_command_capability_new`,
`browser_renderer_command_capability_valid`,
`_require_issued_renderer_reply`, and
`_retire_renderer_command_capability`. Manual step and checker names are frozen
in the system-test plan; incomplete checkers must use its exact `fail(...)`.
Exact owners are frozen: common codec
`src/lib/common/web/browser_renderer_protocol.spl`; host staging/admission
`src/os/hosted/hosted_browser_renderer_process.spl`; worker echo/sequencing
`src/os/hosted/hosted_browser_renderer_worker.spl`; and the existing entropy
facade `src/lib/nogc_sync_mut/io/crypto_sffi.spl`. No compiler, runtime-symbol,
provider, interpreter, dynamic-SFFI, or raw-runtime-symbol lane is added.

| Lane | Bounded ownership | Handoff |
| --- | --- | --- |
| `command_capability_atomic_activation` | one commit promotes the existing SBR2 codec; adds the private parent validator over `crypto_sffi.random_hex(16)`; stages/issues/consumes/retires the tuple; migrates every command, `network_response`, fetch, and frame direction; rejects all legacy schemas | INTEGRATED `879f28bc059`; static-only, with no compatibility flag, fallback, or mixed SBR1/SBR2 state |
| `command_capability_sspec` | focused exact-four-step spec, deterministic parent creator/conversion unchanged-state errors, FIFO separate-read and split-write staged/issued oracles, numeric/payload maxima, lifecycle cleanup, conforming echo, 10k latency/allocation/RSS receipt | source/manual integrated; runtime and 10,000-cycle receipts remain RED |
| `command_capability_final_review` | protocol bounds, causal binding, lifecycle cleanup, backward rejection, manual quality | normal/highest-capability reviewer |

Production source now uses the atomic all-direction SBR2 graph from
`879f28bc059`; legacy production schemas remain fail-closed. This is a
static-source integration statement only. No admitted current full pure-Simple
CLI has supplied runtime or 10,000-cycle evidence.

Lower-model sidecars may enumerate malformed codec fixtures only after these
names are frozen. They may not change entropy policy, weaken fail-closed legacy
admission, introduce negotiation, commit, or push. Root Codex is merge owner;
a separate normal/highest-capability agent is final reviewer. Implementation
may be reviewed by file owner, but promotion is one atomic commit. No lane is
accepted before the focused modern SSpec executes once on an admitted current
full pure-Simple CLI.

### Hosted-parent capability handoff

Frozen interfaces:

- `crypto_sffi.random_hex`
- `browser_renderer_command_capability_valid`
- `browser_renderer_command_capability_new`
- `_require_issued_renderer_reply`
- `_retire_renderer_command_capability`

The integrated manual exposes exactly
`Admit the trusted capability owner`, `Issue one fresh command token`,
`Reject an unissued command token`, and
`Retire all capability material`. Setup/checker names are
`setup_trusted_capability_owner_fixture`,
`check_trusted_capability_owner_admitted`,
`check_fresh_command_token_issued`,
`check_unissued_command_token_rejected`, and
`check_all_capability_material_retired`. Future incomplete replacement helpers
must fail explicitly; they cannot replace the integrated static scenarios.

Security evidence proves page, SimpleScript, JavaScript, common-codec, and
worker paths cannot install or consume parent authority. Codec and worker do
not own or import the private creator. It does not claim that trusted code
cannot format random hexadecimal bytes. The parent-only issued tuple,
complete-wire disclosure, exact correlation, and one-use retirement are the
authority boundary. Deterministic evidence exercises the parent
creator/conversion unchanged-state error path; validator-only evidence cannot
promote the row. Production has no fallback or fault switch.

## Batch-3 held-lane status (2026-07-30)

- Durable Home: production, focused SSpec, canonical generated manual, and
  final normal/high review PASS; held unexecuted and unmerged.
- Nonzero-clock JavaScript timers: production, focused SSpec, generated manual,
  and final normal/high review PASS; held unexecuted and unmerged.
- `<mark>`: production/spec high review PASS, but generated-manual FAIL at the
  three-cycle cap because six raw bullets leak from helper and shutdown text;
  held and unmerged.
- Text overflow: HOLD/FAIL on unresolved CSS-wide cascade behavior.
- Iterative DOM tag search: production/spec static high review PASS, but
  generated-manual FAIL at the three-cycle cap; only preorder assertions were
  folded. It is held and unmerged.

The prior SimpleScript PASS and existing CSS cascade/bookmark-title designs
remain unchanged. These status rows add no executable or merge claim.

## Production continuation batch 5 (2026-07-30)

| Lane | Result | Status / next gate |
| --- | --- | --- |
| `textarea_event_lifecycle` | shared linear CR/LF/CRLF-to-CRLF form normalization for both BrowserSession and SimpleBrowserPage; exact focus/beforeinput/input/change/blur/focusout ordering, UTF-8 POST body, and component-bound Draw IR/Engine2D pixels | final high review PASS; execution HELD for an admitted current pure-Simple full CLI |
| `renderer_fd_launch` | open-once/fd-exec prototype closes pathname TOCTOU, but post-admission identity still compares mutable mtime/ctime and rejects a safely renamed admitted inode | HOLD at three-cycle cap; retain dev/inode/mode/uid/gid/size plus SHA-256, drop timestamps, then rerun the C selfcheck in a fresh cycle |
| `hosted_navigation_visible` | empty executable evidence was removed; the RED plan still lacks an NFR-004 sample/p95 gate, an in-flight delayed Stop fixture, and exact bookmark/compositor/registry/process owners | HOLD at three-cycle cap; repair the contract before creating a hosted SSpec |
| `https_terminal_outcome` | atomic terminal-winner/provider-binding design remains incomplete: counter baselines conflict, authenticated response bytes are not taken before free, and native fd-admission ownership is unnamed | HOLD at three-cycle cap; repair the contract before implementation |
| `html_progress_element` | determinate/indeterminate semantics and bounded Draw IR were prototyped, but Style reconstruction loses specifiedness/accent state, UA em sizing is hardcoded, invalid CSS is marked specified, declarations are parsed twice, and fill math quantizes/overflows | HOLD at three-cycle cap; repair Style ownership and ratio math before reuse |
| `drawir_reuse_wire` | SBRF8 strict-tail/cache/image prototype still revalidates and deep-compares O(commands+resources); final scalar-receipt/skip-submit edit was interrupted uncommitted and statically unverified | HOLD; do not merge `0e2ab0e3ba6` or the uncommitted cycle-3 work; resume from a fresh worktree with constructor/receipt/manual audit |

No batch-5 row promotes full browser production completion. Only the textarea
slice is integrated; its executable status remains HELD. Bootstrap output and
the Rust seed are not admissible evidence.

## Production continuation batch 6 (2026-07-30)

| Lane | Result | Status / next gate |
| --- | --- | --- |
| `bookmark_title_transport` | additive bounded SBRF8 title witness, generation/reply/URL trust binding, lifecycle clears, production parent Favorite routing, atomic SQLite mutation+snapshot rollback, restart/UI parity, and forged 513-byte pre-decode rejection | final high review PASS; integrated STATIC / EXECUTION HELD |
| `command_capability_codec` | SBR2 framing, bounds, canonical trailer, resequencing, and atomic parent/worker/nested production migration | INTEGRATED `879f28bc059`; STATIC-ONLY, runtime and 10,000-cycle evidence remain RED |
| `command_entropy_hardening` | existing `rt_random_hex` now uses portable fallible OS entropy, native/interpreter NIL parity, and guaranteed zeroization; dynamic SFFI is unchanged | final high review PASS; the existing `crypto_sffi.random_hex(16)` facade is the selected SBR2 entropy seam |
| `negative_z_index` | signed/context/paint-hit prototype closes most local defects, but `revert`/`revert-layer` can retain an earlier integer and create a visible stacking regression without cascade provenance | HOLD at three-cycle cap; do not merge `b9ad3eff8f1` |
| `radio_event_lifecycle` | external form ownership and lifecycle prototype still lacks one O(N) generation-qualified document identity index across events, edits, bridge sync/replacement, grouping, and submission | HOLD at three-cycle cap; do not merge `220355ca427` |
| `js_property_storage_gc` | indexed property prototype leaves physical-order readers, tombstone roots, arbitrary detached graphs, omitted roots, and stale numeric-ID aliasing | HOLD; do not merge `d2d08cf2eb0`; requires full GC/generation-qualified handle architecture |

No batch-6 static PASS promotes full production completion. Bookmark execution
and SBR2 runtime/10,000-cycle evidence remain RED until an admitted current
pure-Simple artifact supplies focused executable evidence.

## Production continuation batch 7 (2026-07-30)

| Lane | Result | Status / next gate |
| --- | --- | --- |
| `address_input_bound` | strict single-pass UTF-8/control validation, centralized 2048-byte raw bound, and validate-before-mutate behavior across BrowserSession, worker, hosted web, registry, and live entry | final high review PASS; integrated STATIC / EXECUTION HELD |
| `durable_home` | additive profile migration, bounded atomic Home save/load, startup seeding for primary and registry owners, legacy/corrupt fallback, restart navigation, and exact Home chrome evidence | final high review PASS; integrated STATIC / EXECUTION HELD |
| `animation_shared_clock` | shared JS/SimpleScript/CSS clock prototype still performs unchecked interval reschedule/refresh due arithmetic and can wrap/spin at `i64::MAX` | HOLD at three-cycle cap; do not merge `a6079d95168` |
| `label_activation` | prototype lacks document-generation-safe routes and activation reentrancy/interactive-descendant handling; order/manual/pixel evidence remains incomplete | HOLD; do not merge `0cd983b1050` |
| `simplescript_listeners` | prototype has attribute-name injection, stale route retargeting, missing render/JS invalidation, unbounded O(A*N) dispatch, and non-reproducible evidence | HOLD; do not merge `8da4cbc2b30` |

No batch-7 row supplies fresh target-runtime PASS. The integrated source and
design rows remain execution-held or explicitly RED; bootstrap and Rust-seed
evidence remain inadmissible.

## Intensive HTML/CSS and animation batch 8 (2026-07-30)

| Lane | Owner | Scope | Status / gate |
| --- | --- | --- | --- |
| `dom_identity_design` | `dom_identity_design` | Freeze one generation/index owner and fold label/radio/listener consumers into the canonical lanes below | INTEGRATED STATIC CANDIDATE; target runtime/NFR evidence HELD |
| `html_hr` | `simplescript_listeners_current` | Native separator defaults plus exact authored border clearing through canonical WebIR/DrawIR/Engine2D | FINAL REVIEW PASS; integrated static evidence, execution HELD |
| `html_fieldset_legend` | `fieldset_legend_render` | Bounded semantic/UA fallback, authored border clearing, exact DrawIR/Engine2D pixels | FINAL REVIEW PASS; integrated Partial/RED boundary, draft manual, execution HELD |
| `animation_publication_cache` | `animation_perf_lifecycle` | Remove full-document rebuild from the real hosted animation-frame publication path | FINAL REVIEW PASS; integrated static evidence, numeric runtime evidence HELD |
| `animation_runtime_evidence` | root merge owner | Admit the current pure-Simple CLI by source receipt before any focused execution | HELD: binary hash exists but no matching source/build receipt has been found |

The capped fractional-animation, negative-z, label, radio, clock, and prior
listener prototypes remain HOLD. This batch must not retry them, add a private
paint path, or treat parsing/source inspection as rendering or animation
evidence. Root Codex is merge owner and final reviewer; no sidecar pushes.

## Production browser batch 9 (2026-07-30)

| Lane | Bounded owner | Acceptance boundary | Status |
| --- | --- | --- | --- |
| `dom_identity_owner_impl` | canonical `dom_identity_index.spl` only | O(N) immutable index, generation routes, duplicate-ID/form-owner rules, four-step RED-first SSpec | HOLD: `a20520e28a7` adds an always-failing active spec, boolean-wrapper assertions, and incorrect `img` form association; do not merge |
| `html_css_definition_list` | one uncapped Partial semantic row | canonical WebIR/DrawIR/Engine2D geometry and exact pixels; no private painter | FINAL STATIC REVIEW PASS; integrated, target execution HELD |
| `navigation_controls_batch9` | one uncapped Go/Back/Forward/Stop/Home/URL/Bookmark defect | public actions, lifecycle authority, exact state/UI evidence | STATIC REVIEW PASS: one candidate rule rejects `about:blank`/capacity overflow and keeps Favorite enablement/action results truthful; durable profile commit remains separate |
| `https_sandbox_batch9` | one uncapped HTTPS/sandbox boundary | fail closed with hostile evidence; no provider/runtime shortcut | STATIC REVIEW PASS: shared origin gate rejects duplicate headers and ports outside 1..65535; target execution HELD |
| `pure_simple_receipt_admission` | existing self-hosted artifact/receipt path | SHA-256 + source tree/revision + build mode/command; mtime/version are insufficient | AUDIT COMPLETE: deployed hash `79ca755d...5173a7` has no matching receipt; deploy drops/invalidates Stage4 provenance |
| `event_routing_batch9` | one uncapped button/text-input route defect | real pointer/keyboard/input actions and canonical state/pixels | CRASHED BEFORE DEFECT SELECTION; no production claim |

All lanes start from pushed main `b26c4ae776d`. They may not reopen a
three-review capped HOLD, run a full bootstrap, use the Rust seed, or claim
target execution without an admitted pure-Simple receipt. Root Codex remains
merge owner; independent normal/high-capability review is mandatory before
integration.

The batch was interrupted by host instability while unrelated Simple tests
held multiple gigabytes of RSS. Recovery used commit-object review and one
sparse checkout only; no full checkout, bootstrap, or target execution was
started. Missing temporary worktrees are not evidence.

## Generation-qualified DOM identity implementation lanes

<!-- codex-design -->

Status: **STATIC EVIDENCE PRESENT / SOURCE HOLD-RED / TARGET EXECUTION HELD**. Frozen names are
`DomDocumentGeneration`, `DomNodeRoute`, `DomRadioGroupKey`,
`DomIdentityIndex`; manual steps are `Build the document identity index`,
`Dispatch through stable routes`, `Replace the document during a handler`,
and `Reject stale routes and release the index`. Frozen helpers are
`setup_dom_identity_generation_fixture`, `check_dom_identity_index_built`,
`check_stable_route_dispatch`, `check_document_replacement_during_handler`,
and `check_stale_routes_and_index_release`; each checker now invokes production
owners with direct assertions and no placeholder pass.

Design-audit status: **FOCUSED SSpec/MANUAL PRESENT; COOKIE-QUEUE AND ISOLATED
STALE-CLEANUP SOURCE REPAIRS REQUIRED; RUNTIME/NFR RECEIPTS HELD**.

The integrated session surface is `document_generation`,
`current_dom_identity_index`, `route_for_layout_target_key`,
`layout_target_key_for_route`, `author_id_for_route`, and the single staged
`publish_dom_snapshot` commit boundary. Lane 5 evidence lives at
`test/03_system/app/browser/feature/browser_dom_identity_generation_spec.spl`
and its exact `doc/06_spec/...` mirror; the 10,000-cycle numeric receipt remains
held.

| Order | Lane | Exact ownership | Acceptance / dependency |
| --- | --- | --- | --- |
| 1 | `dom_identity_index_owner` | Add import-free `dom_limits.spl` owning only `HTML_MAX_TREE_DEPTH`/`HTML_MAX_NODES`, move `html_tree_builder.spl` to those imports, and add `dom_identity_index.spl`; two-pass O(N) build, route/layout-key parsing, association queries, counters | integrated static candidate; execution held |
| 2 | `dom_accessor_form_migration` | `dom_accessors.spl`, `browser_session_form.spl`; replace recursive identity/form/label/radio/event-path scans | integrated static candidate; execution held |
| 3 | `dom_dispatch_bridge_migration` | `dom.spl`, `browser_session.spl`, `browser_session_runtime.spl`, `browser_session_loading.spl`, `script/script_host.spl`, `script/simple_script.spl`, `script/event_api.spl`, and `js/dom_bridge.spl`; typed event routes, atomic DOM/index/script/listener publication, focus/Space/edit/blur, label/radio actions, and shared reentrant budget | HOLD/RED: rejected eval leaks pending cookie-write queue; rollback oracle present |
| 4 | `dom_ui_hosted_migration` | `browser_session_ui_access.spl`, `hosted_web_content_session.spl`, `hosted_browser_renderer_worker.spl`; consume `route_for_layout_target_key` through the session generation gate; generation-bound snapshots and press/release/focus routes | HOLD/RED: isolated stale cleanup incomplete; parity oracle present |
| 5 | `dom_identity_sspec` | focused modern SSpec, mirrored manual, N/2N and 10,000-cycle production receipts | SSpec/manual and held receipt schema present; numeric/runtime receipt held |

Exact production ownership:

- Lane 1:
  `src/lib/gc_async_mut/gpu/browser_engine/dom_limits.spl`,
  `src/lib/gc_async_mut/gpu/browser_engine/html_tree_builder.spl`, and
  `src/lib/gc_async_mut/gpu/browser_engine/dom_identity_index.spl`.
- Lane 2:
  `src/lib/gc_async_mut/gpu/browser_engine/dom_accessors.spl` and
  `src/lib/gc_async_mut/web/browser_session_form.spl`.
- Lane 3:
  `src/lib/gc_async_mut/gpu/browser_engine/dom.spl`,
  `src/lib/gc_async_mut/web/browser_session.spl`,
  `src/lib/gc_async_mut/web/browser_session_runtime.spl`,
  `src/lib/gc_async_mut/web/browser_session_loading.spl`,
  `src/lib/gc_async_mut/gpu/browser_engine/script/script_host.spl`,
  `src/lib/gc_async_mut/gpu/browser_engine/script/simple_script.spl`,
  `src/lib/gc_async_mut/gpu/browser_engine/script/event_api.spl`, and
  `src/lib/gc_async_mut/gpu/browser_engine/js/dom_bridge.spl`.
- Lane 4:
  `src/lib/gc_async_mut/web/browser_session_ui_access.spl`,
  `src/os/hosted/hosted_web_content_session.spl`, and
  `src/os/hosted/hosted_browser_renderer_worker.spl`.

Lower-model sidecars may inspect one owner per lane only after Lane 1 lands;
they may not rename this API or add label/radio/listener identity maps. Merge
owner is the browser-hardening coordinator. Final acceptance requires the best
available normal/highest-capability review of the combined source/spec/manual
diff and one admitted target-runtime execution.

Migration is not piecemeal: Lanes 1-4 are now assembled in one static review
tree, but target execution remains held. Lane commits remain review artifacts
until the combined candidate is accepted. The merge deletes
`be_dom_event_identity` as routing identity and its `node:<node_id>` fallback,
`be_dom_route_identity`, `be_dom_route_node_id`,
`be_dom_matches_identity`, `be_dom_event_identity_at_element_path`,
`be_dom_layout_target_key`, `_be_dom_find_path_to_identity`,
`be_dom_find_path_to_id`, `_be_dom_implicit_submit_blocker_count`,
`be_dom_form_allows_direct_implicit_submit`,
focus/form/default/dispatch `*_id` routing, every
NUL `route-node:` branch, text `BeDomEvent`/event-api/dispatch routes,
`_script_host_apply_event_action_to_id`,
`script_host_apply_action_to_id`, `BrowserRuntimeState.dom_node_ids` and
separate bridge generation, bare Space/selection/hosted press/focus fields,
`JsDomListener.node_id`, `_browser_dom_target`, and every runtime recursive
consumer. The normative file-by-file census and renderer-only `node_id`
exclusions are in the detail design; any omitted production consumer blocks
the combined merge. Label, radio, and SimpleScript HOLDs remain non-mergeable
until this prerequisite lands.

Lane 1 owns the shared limit relocation because the identity index cannot
import private web/session constants. Lane 3 is the sole merge owner for typed
event and script state: page-visible author-ID strings are projections only,
and candidate DOM/index/bridge/listener state publishes or rolls back
together, including load-time bindings and both script runner roots. Lane 4
captures the frame generation and calls the session
`route_for_layout_target_key` gate exactly once per hit; it never retries an
old layout key against a replacement document.

Lane 2 retains a single O(N) implicit-submit control traversal, but it accepts
a form route and consults indexed form ownership rather than recursively
recomputing association. Generic recursive selector compatibility is outside
routing; production author lookup remains O(1) through
`route_for_author_id`, and an absent author ID has no `node:<node_id>`
projection.

## Production navigation batch 9 (2026-07-30)

| Lane | Root cause and bounded fix | Status / gate |
| --- | --- | --- |
| `favorite_mutation_truth` | `BrowserSession.add_current_favorite` discarded the admission result while UI access always exposed Favorite as enabled, so a fresh session could store the non-network `about:blank` URL and report success. One shared candidate rule now rejects it and capacity overflow; the public UI route disables or rejects impossible session-local mutations. | STATIC TDD COMPLETE; exactly four public UI-access steps and mirrored manual; durable profile commit is a separate owner; execution HELD for a source-admitted current pure-Simple CLI |

The capped history-ledger, primary-close, stale-pressed navigation chrome, and
hosted-navigation-visible lanes were not retried. Page Draw IR pixels are not
claimed for the parent-owned textual chrome control.

## Production browser crash-recovery batch 10 (2026-07-30)

| Lane | Root-cause result | Status |
| --- | --- | --- |
| `script_resource_bound` | The shared event loop now caps timer and animation-frame queues at 256, including direct callers; draining restores scheduling. | INTEGRATED `d4ffb28dae4`; static review PASS, target execution HELD |
| `associated_form_controls` | Submission now traverses document order and uses canonical form ownership, so external `form="..."` controls are included and sibling-form controls are excluded. | INTEGRATED `d4ffb28dae4`; modern SSpec/manual present, target execution HELD |
| `https_ipv6_authority` | All three HTTP URL parsers structurally validate bracketed IPv6, including compression and final embedded IPv4, and browser admission reuses the parser. | INTEGRATED `d4ffb28dae4`; parser/browser truth tables present, target execution HELD |
| `sandbox_stateful_commit` | A pending document commit now rejects a stateless legacy renderer frame before URL/history mutation and tears down broker state. | INTEGRATED `d4ffb28dae4`; adversarial SSpec/manual present, target execution HELD |
| `renderer_site_swap_release` | Site swap invalidates the prior frame receipt and clears retained raster/image state before the replacement process becomes ready. | INTEGRATED `d4ffb28dae4`; live-starting replacement discriminator present, target execution HELD |
| `navigation_home_gate` | Proposed empty-home gate contradicted the canonical `about:blank` session state. | REJECTED; `ca3a3cffa9f` must not merge |
| `cross_origin_image_credentials` | Proposed unconditional credential omission exceeded the standard image-fetch boundary. | REJECTED; `21f57875664` must not merge |

Recovery used isolated commit trees and one static verification pass. No
bootstrap, Rust seed, or repeated crashing target command was used. Qualified
pure-Simple execution/docgen remains blocked by the recorded self-hosted
interpreter string-interpolation defect.

## Production browser batch 11 (2026-07-30)

| Lane | Result | Status |
| --- | --- | --- |
| `html_css_rendering` | No remaining uncapped one-defect rendering gap was proven; broader feature rows stay planned. | AUDIT COMPLETE / NO CHANGE |
| `fieldset_events` | Effective disabled state is propagated during the existing O(N) control traversal, including the first-legend exception. | INTEGRATED `0d6c055a489`; public UI-action SSpec/manual present |
| `document_redirect` | An unresolved redirect URL is rejected before permit, provisional origin, or pending document commit creation. | INTEGRATED `0d6c055a489`; hostile exact-error SSpec/manual present |
| `script_body_animation` | Changed SimpleScript body assignments advance the existing single UI revision and reconcile CSS animation instances; identical assignments remain no-ops. | INTEGRATED `0d6c055a489`; timer→DOM→DrawIR discriminator present |
| `gpu_image_retention` | The retained table now contains only current-frame resources while validated references survive consecutive frames. | INTEGRATED `0d6c055a489`; release/reuse SSpec/manual present |
| `profile_revocation` | Treating `_ensure(..., false)` as revocation also disabled profile access on ordinary page pointer dispatch. | REJECTED; `2ffa73f48c9` must not merge |
| `interpreter_interpolation` | Post-parse expansion promotes valid regions to canonical `EXPR_INTERPOLATED_STRING`; evaluation no longer parses source. | INTEGRATED STATIC `ae4c3d56ce3`; phase-2/3 and focused SSpec execution HELD |

The compiler lane used independent static review and did not start another
bootstrap while concurrent sessions owned the shared cache and full-bootstrap
processes. Its failed seed delegation probe is recorded as a failure, not PASS.

## Production browser batch 12 (2026-07-30)

| Lane | Result | Status |
| --- | --- | --- |
| `focus_editability_order` | The shared edit owner re-resolves the focused target and rechecks mutability after `focus`, before `beforeinput`. | INTEGRATED `8f2ae532371`; modern public-action SSpec/manual present |
| `address_draft_revision` | A successful changed address draft advances the canonical UI-access revision; invalid and identical drafts do not. | INTEGRATED `8f2ae532371`; canonical address lookup and modern SSpec/manual present |
| `script_cookie_partition` | Script cookie admission synchronizes the validated active document origin before deriving the partition key. | INTEGRATED `8f2ae532371`; hostile stale-origin SSpec/manual present |
| `html_blockquote` | Native `blockquote` UA semantics lower through Web layout, Draw IR, and Engine2D exact pixels. | INTEGRATED `8f2ae532371`; bounded selected-profile SSpec and complete manual present |
| `script_cancellation` | Existing timer, interval, animation-frame, and listener cancellation paths are bounded and covered; no distinct defect was found. | AUDIT COMPLETE / NO CHANGE |
| `renderer_release` | Existing document replacement/close and current-frame retention owners release listeners, images, and retained render state; no distinct defect was found. | AUDIT COMPLETE / NO CHANGE |

All changed lanes received independent static review. Static diff, spec-layout,
placeholder, and direct-environment guards passed once. Target execution and
docgen remain HELD because no source-admitted pure-Simple artifact exists at or
after `ae4c3d56ce3`; no bootstrap or seed substitute was used.

## Production browser batch 13 (2026-07-30)

| Lane | Result | Status |
| --- | --- | --- |
| `html_header` | Existing native header semantics now have exact Web layout, Draw IR, and Engine2D evidence. | INTEGRATED `9f720c62c72`; selected-profile count is 9 |
| `padding_cascade` | One linear resolver honors valid shorthand, physical, and horizontal-LTR logical source order while malformed declarations cannot win. | INTEGRATED `9f720c62c72`; ASCII whitespace scan is linear |
| `fractional_opacity_siblings` | Safe same-size clipped siblings lower to cropped, aggregate-viewport-bounded opacity batches; unsafe backdrop or differing-size cases fall back. | INTEGRATED `9f720c62c72`; single Engine2D pool preserved |
| `signed_css_time` | Negative seconds and milliseconds retain sign, including symmetric fractional-millisecond rounding. | INTEGRATED `9f720c62c72`; exact consecutive frame evidence present |
| `script_animation_epoch` | Unrelated SimpleScript stylesheet replacement reuses unchanged animation signatures instead of restarting their epoch. | INTEGRATED `9f720c62c72`; revision, stylesheet, Draw IR, and pixel evidence present |
| `completed_handle_refresh` | Completed Node-compatible timer handles cannot re-enter a full shared queue; paired handle arrays remain bounded. | INTEGRATED `9f720c62c72`; truthful JS/Node unit scope, not browser reachability |

Independent reviews rejected and corrected full-viewport opacity work,
offscreen-size pool thrashing, quadratic whitespace scanning, incomplete
mutation evidence, negative-millisecond loss, and false browser reachability.
Static guards passed once. Qualified pure-Simple execution/docgen remain HELD.

## Production browser batch 14 (2026-07-30)

| Lane | Result | Status |
| --- | --- | --- |
| `bookmark_title_witness` | Bounded canonical `SBRF8` title evidence is generation/reply/URL-bound and persists through public remove/re-add plus profile/UI reopen. | INTEGRATED `15b6727a5ce`; static high review PASS |
| `renderer_loader_environment` | The real sandbox spawn path starts with an empty child environment; a hostile C probe covers representative loader variables. | INTEGRATED `15b6727a5ce`; REQ-014/021 only, runtime execution HELD |
| `js_lexical_parent` | The canonical production environment stack rejects invalid raw parents before allocation and bounds corrupt-chain traversal. | INTEGRATED `15b6727a5ce`; REQ-017 prerequisite only, GC remains RED |
| `chrome_press_generation` | Site swap clears active/pending press ownership before replacement; immediate/retry release accounting is exactly once. | INTEGRATED `15b6727a5ce`; exact Draw IR/Engine2D evidence present |
| `fractional_animation_boundaries` | Token-exact shorthand parsing preserves last-valid source order and animation clocks saturate at i64 bounds. | INTEGRATED `15b6727a5ce`; 11/11 modern static scenarios/manual |
| `content_visibility_salvage` | Current shared O(N) GPU paint-state guard already supersedes the orphan candidate. | AUDIT COMPLETE / NO CHANGE |
| `simple_script_listeners` | Reconstructed candidate lacked generation-qualified detached-node identity, public unlisten reachability, and aggregate lifecycle accounting. | WITHDRAW `07d7476562a`; depends on DOM identity lanes 1-4 |
| `stage4_admission` | No clean provenance-qualified full CLI includes the current compiler/browser source. | HELD; no target execution/docgen |

All accepted lanes received independent normal/high-capability static review.
The combined diff/layout/placeholder/direct-environment guards passed once.
No bootstrap, seed fallback, stale artifact, or runtime PASS was used.

## Production browser batch 15 (2026-07-30)

| Lane | Result | Status |
| --- | --- | --- |
| `csp_animation_clock` | Script-denying CSP advances the sole browser clock, then returns before JS/SimpleScript timers or rAF; CSS frames still progress. | INTEGRATED `b0f47f6aac0`; exact Draw IR/Engine2D evidence |
| `invalid_form_method` | Missing/empty/invalid methods use GET; valid GET/POST remain exact; unsupported `dialog` and forbidden transport fail before network. | INTEGRATED `b0f47f6aac0`; public-action evidence |
| `canonical_drawir_upload` | Web upload and comparison consume the identical composition through the shared Engine2D helper with real result receipt and full-frame absolute oracle. | INTEGRATED `b0f47f6aac0`; private CPU route removed |
| `details_summary` | Omitted-p parsing, first-summary visibility, nested/interactive activation, cancellation, and post-animation suppression are O(N) and canonical. | INTEGRATED `d25b474cf0f`; HTML bounded rows now 11 |
| `raf_alignment` | rAF deadlines align to document origin, nested callbacks defer, refresh metadata remains aligned, and capped wakeups saturate safely at i64 bounds. | INTEGRATED `d25b474cf0f`; exact callback/frame evidence |
| `sbr2_capability` | Existing entropy facade + common validator + private parent issuance are reconciled across architecture/TLDR/detail/agent/system-test docs. | DESIGN `d25b474cf0f`, production integrated `879f28bc059`; STATIC-ONLY, runtime/10,000-cycle RED |
| `stage4_admission` | No clean full CLI includes current compiler/browser source. | HELD; no runtime/docgen PASS |

All implementation lanes received independent normal/high-capability static
review. Review caught CSP ordering, form `dialog`, correlated pixel evidence,
summary interactive precedence, rAF deadline/wakeup overflow, and SBR2
authority-model contradictions before integration. Two combined static guard
passes succeeded; no bootstrap, seed fallback, or stale runtime was used.

## Production browser batch 16 status (2026-07-30)

| Lane | Result | Status |
| --- | --- | --- |
| `broker_hsts_policy` | Trusted broker owns HSTS upgrade/learning decisions. | PUSHED `6e7b4517a81`; runtime evidence remains unclaimed |
| `generated_dom_identity` | Atomic generation-qualified DOM identity contract. | DESIGN PUSHED `ac847fbfb67`; PROPOSED/RED, not implemented |
| `crash_safe_sbr2` | Renderer traffic is bound to one-use SBR2 capabilities on the SBR2 base. | PUSHED `879f28bc059`; STATIC-ONLY, no 10,000-cycle/runtime PASS |
| `stage4_admission` | No provenance-qualified current full pure-Simple CLI was admitted. | NONE; available artifacts are stale-lineage |
| `js_vm_reclamation` | Candidate used reusable raw IDs, non-refcounted escaped roots, and property-name-inferred numeric edges. | REJECTED; requires generation-qualified handles, independent-owner refcounts, and typed mark edges |
| `parent_history` | Capability-bound parent ledger builds on the SBR2 base. | INTEGRATED `2e188a745d9`; STATIC/EVIDENCE-HELD, no runtime PASS |

The rejected pre-SBR2 history candidate remains non-mergeable; the superseding
parent history integration is `2e188a745d9`. These rows record integration and
design state only; they do not claim runtime PASS or implementation completion.

## Production browser batch 17 reconciliation (2026-07-30)

| Lane | Result | Status |
| --- | --- | --- |
| `html_figure` | Selected-profile figure UA margins lower through canonical Web layout, Draw IR, and Engine2D evidence. | INTEGRATED `897368fb592`; STATIC/EVIDENCE-HELD |
| `js_vm_reclamation_design` | Generation-qualified external handles, independent-owner refcounts, and typed mark edges are frozen. | DESIGN `ef90c16b194`; PROPOSED/RED, not implemented |
| `live_post_listener_activation` | Default actions revalidate live node identity after listener dispatch. | INTEGRATED `ca4769405d6`; STATIC/EVIDENCE-HELD |
| `stage4_provenance_real_motion` | Provenance and real-motion wrappers reject stale/noncurrent evidence. | `6c76b8ac0c0` wrapper self-tests PASS; no target runtime execution |
| `parent_history` | Parent-authoritative history is capability-bound to the production SBR2 graph. | INTEGRATED `2e188a745d9`; STATIC/EVIDENCE-HELD |
| `stage4_admission` | Audit at `/tmp/simple-history-h1.d3de` and the active build found no provenance-qualified current full CLI. | NONE; active build remains stale-lineage |
| `html_menu` | Selected-profile `<menu>` UA spacing lowers through the canonical Web layout path. | PUSHED `b107a4e2a9e`; STATIC/EVIDENCE-HELD |
| `js_vm_reclamation_g2` | The operative `std.js.types` raw-i64 ABI lacks lexical-parent identity, generations, free-list state/counters, typed edges, and external-root ownership; its symbol contract mismatches the planned implementation. | BLOCKED / NO COMMIT; complete repository-wide A-through-E migration before implementation |

No Batch-17 row supplies runtime, docgen, 10,000-cycle, or full-browser
completion evidence. Generation-safe GC design `ef90c16b194` remains
PROPOSED/RED; neither the G2 lane nor this addendum completes the goal.

## Production browser batch 18 final reconciliation (2026-07-30)

Exact repository HEAD:
`9653a09fdea118b5d502fa06989d83e12cd4fe19`.

| Lane | Result | Status |
| --- | --- | --- |
| `html_small_ua` | Selected medium-UA `<small>` sizing lowers through canonical style, layout, Draw IR, and absolute pixels. | INTEGRATED `b9e1a0e6707`; STATIC/EVIDENCE-HELD |
| `js_store_kind_design` | Heap stores are distinguished from edge semantics in the frozen reclamation design. | DESIGN `f8b926e0dd5`; RED, not implemented |
| `script_mime_boundary` | One canonical media-type gate normalizes parameters/case and rejects invalid classic/module responses before hostile state publication. | INTEGRATED `2211d8ae1b5`; STATIC/EVIDENCE-HELD |
| `hsts_history_traversal` | Back/Forward bind the HSTS-upgraded off-side ledger to SBR2 capability and publish only after validator acceptance. | INTEGRATED `416ccc6efb8`; STATIC/EVIDENCE-HELD |
| `input_button_keyboard` | Enter/Space keyboard activation reaches canonical input-button default action with exact cancellation/repeat behavior. | INTEGRATED `e9b50343645`; STATIC/EVIDENCE-HELD |
| `drawir_text_transform` | Canonical Draw IR text uses transformed/RTL visual text consistently for metrics and every text-command path. | INTEGRATED `e7af94e921c`; STATIC/EVIDENCE-HELD |
| `gpu_paint_shape_key_scaling` | Ordered `x,y,w,h;` identity now uses the existing chunked `StringBuilder` rather than cumulative immutable-prefix concatenation. | INTEGRATED `9653a09fdea`; performance SSpec HELD/UNMEASURED |
| `stage4_admission` | The active `4cdd` build is dirty/stale and has no provenance receipt. | NONE; no runtime/docgen/performance admission |
| `D1` | Local candidate `1728` remains held. | DO NOT MERGE |
| `D2` | Review lane stopped without a commit. | PENDING REVIEW / UNMERGED |

Root production-browser coordinator remains merge owner and final reviewer.
The bounded static integrations do not supply a target-runtime, docgen,
10,000-cycle, performance, full-browser, or goal PASS. No bootstrap or stale
artifact may substitute for Stage-4 admission.

## Production browser batch 19 reconciliation (2026-07-30)

Exact repository HEAD:
`165d7b3a8c799163e99321c56d0b4310c3b79fb4`.

| Lane | Result | Status |
| --- | --- | --- |
| `stage4_admission` | The `807182` full-CLI build is dirty, divergent from current source, and has no provenance receipt. | NONE; no runtime/docgen/performance admission |
| `html_abbr_inline_flow` | Native `<abbr>` remains in inline flow and lowers through the existing text Draw IR path. | INTEGRATED `8beb64585b2`; STATIC/EVIDENCE-HELD |
| `css_duplicate_keyframe_offset` | Equal-offset keyframes cascade once in source order, retaining distinct earlier properties while later same-property declarations win. | INTEGRATED `2078c3dfab4`; STATIC/EVIDENCE-HELD, runtime unavailable |
| `attachment_navigation_boundary` | Hosted navigation rejects attachment activation before publication across the policy/session/process boundary. | INTEGRATED `165d7b3a8c7`; STATIC/EVIDENCE-HELD |
| `D1` | Held dispatch candidate remains on lineage through `06dc5620781`. | DO NOT MERGE |
| `D2` | Held dispatch candidate remains on lineage through `06dc5620781`. | DO NOT MERGE |
| `D3` | Remaining production call sites are `SimpleScriptExecutor.reset` ×2 and `BrowserRuntimeState.bind_dom` ×3 in `browser_session_runtime`, plus `SimpleScriptExecutor.bind_dom(current_dom)` ×2 and `state.bind_dom`/`BrowserRuntimeState.bind_dom` ×2 in `browser_session_loading`; SSpec, manual, and final review are incomplete. Lane 4 is untouched. | STOPPED / UNCOMMITTED |

Root remains merge owner and final reviewer. Batch 19 does not change existing
inventory/scenario accounting except where the canonical HTML/CSS plan
explicitly reclassifies `<abbr>` and extends the animation row. No runtime,
docgen, performance, full-browser, goal, or aggregate HTML/CSS PASS is claimed.

## Production browser batch 20/21 reconciliation (2026-07-30)

Exact repository HEAD:
`08de37b0902b3d703f3d1731ba2f44dc6c18b1a9`.

| Lane | Result | Status |
| --- | --- | --- |
| `stop_pointer_retirement` | Stop retires parent pointer ownership only after command admission, retains committed content/resources, and rejects a stale release. | INTEGRATED `a05a0e96e3e`; STATIC/UNEXECUTED |
| `css_implicit_keyframe_endpoints` | Per-property omitted keyframe endpoints synthesize the underlying value; incompatible values interpolate discretely. | INTEGRATED `0e4b75b167b`; STATIC/UNEXECUTED |
| `html_time_inline_flow` | Native `<time>` matches `<span>` inline geometry, Draw IR text, and pixels while a forced block remains the negative control. | INTEGRATED `7b290473ae6`; STATIC/UNEXECUTED |
| `js_microtask_fifo` | Promise microtasks drain through a FIFO cursor and compact once at the callback cap instead of copying every remaining prefix. | INTEGRATED `055605e866c`; STATIC/UNEXECUTED, PERFORMANCE UNMEASURED |
| `disabled_control_pointer` | Hosted pointer input suppresses effectively disabled controls, including disabled-fieldset ancestry, while retaining the first-legend exception. | INTEGRATED `55a5e9552b2`; STATIC/UNEXECUTED |
| `history_form_state` | Back/Forward restores bounded serialized edited controls while Reload rebuilds committed source. | INTEGRATED `d78e613f3d2`; STATIC/UNEXECUTED |
| `js_timer_heap` | Pending timers use nextTick, deadline, and creation-id heap order while preserving cancellation, interval, and 4,096-task ordering. | INTEGRATED `cbb8027d556`; STATIC/UNEXECUTED, PERFORMANCE UNMEASURED |
| `https_303_head` | HTTPS 303 preserves GET/HEAD, rewrites other methods to GET, and strips representation headers only on rewrite. | INTEGRATED `fb451aa9914`; STATIC/UNEXECUTED |
| `bookmark_snapshot_revision` | Logical bookmark changes advance one revision, no-ops remain stable, and revision-qualified target IDs reject stale shifted bookmarks. | INTEGRATED `a95537545d3`; STATIC/UNEXECUTED |
| `logical_sizing_writing_mode` | Logical size/min/max declarations map through the final inherited/important writing-mode axis with authored-order, Draw IR, and Engine2D controls. | INTEGRATED `08de37b0902`; STATIC/UNEXECUTED |
| `D3` | Generation-qualified DOM dispatch has one remaining `document_route` optional/non-optional type blocker. | HELD / STOPPED / UNCOMMITTED; no SSpec/manual/merge/PASS |
| `security_authority_921fd1` | The renderer authority candidate permits renewable authority instead of one-use consumption. | REJECTED / P0; not pending or accepted |
| `stage4_admission` | No provenance-qualified current full CLI has been admitted for this tranche. | NONE; no runtime/docgen/performance admission |

Root remains merge owner and final reviewer. These static integrations do not
supply a target-runtime, docgen, performance, aggregate HTML/CSS, full-browser,
or goal PASS.

## Production browser batch 22/23 reconciliation (2026-07-31)

Exact repository HEAD:
`8372ca9607fb6f6ee8fda40c19ff3f573350bbe4`.

| Lane | Result | Status |
| --- | --- | --- |
| `trusted_request_redirect_scheme` | Redirect downgrade checks use the trusted request scheme rather than response-controlled scheme text. | INTEGRATED `4a141af30d5`; STATIC/EVIDENCE-HELD |
| `address_selection_backspace` | Backspace clears a fully selected address through each hosted chrome route without disturbing the committed page. | INTEGRATED `5f0758db126`; STATIC/EVIDENCE-HELD |
| `flex_column_gap_wrap` | Flex row wrapping includes column gap before admitting the next item. | INTEGRATED `d620217fb0c`; STATIC/EVIDENCE-HELD |
| `redirect_mixed_content_recheck` | A trustworthy loopback redirect is rechecked before following an ordinary HTTP target. | INTEGRATED `59cbfff9857`; STATIC/EVIDENCE-HELD |
| `finite_animation_terminal_cache` | Finite terminal animation artifacts remain timed, reusable, and distinct from untimed static cache entries. | INTEGRATED `1671c187b9f`; STATIC/EVIDENCE-HELD |
| `input_event_payload` | Input listeners receive exact insertion/deletion payloads and input types before canonical Draw IR publication. | INTEGRATED `c2013e78545`; STATIC/EVIDENCE-HELD |
| `address_url_reference` | URL-reference address forms resolve against the committed document before the absolute URL crosses the worker wire. | INTEGRATED `8372ca9607f`; STATIC/EVIDENCE-HELD |
| `animation_lifecycle_47df` | The lifecycle-event candidate is outside current origin and is not accepted evidence. | REJECTED `47df593f600`; NOT IN `origin/main` |
| `cookie_authority_921fd1` | Renewable renderer authority violates one-use consumption. | REJECTED / P0; not pending or accepted |
| `cookie_authority_protocol` | The distinct protocol repair did not converge. | STOPPED / UNCOMMITTED |
| `D3` | Generation-qualified DOM dispatch remains incomplete. | HELD / STOPPED / UNCOMMITTED |
| `iframe_sandbox_boundary` | Current iframe Draw IR design has no child sandbox-origin or broker-capability contract and leaves script sharing, navigation, and input unsupported. | ARCHITECTURE GAP / RED |
| `stage4_admission` | No provenance-qualified current full pure-Simple CLI is admitted. | NONE; no runtime/docgen/performance claim |

Intervening compiler, GPU, and documentation commits are concurrent ancestry
only and are neither reviewed nor claimed by this browser reconciliation.
Root remains merge owner and final reviewer. No inventory count, runtime,
docgen, performance, aggregate HTML/CSS, full-browser, or goal PASS changes.

## Production browser batch 24/25 reconciliation (2026-07-31)

Composition base:
`745e12de62dded9dab51e023e316649df2c1394f`.

| Lane | Result | Status |
| --- | --- | --- |
| `table_collapsed_border_width` | Collapsed-border conflicts prefer width before style. | INTEGRATED `d01ff82c92a`; STATIC/EVIDENCE-HELD |
| `input_reset_ui_access` | Reset inputs are discoverable and activatable through canonical pointer and keyboard UI access. | INTEGRATED `8ce17d741ca`; STATIC/EVIDENCE-HELD |
| `renderer_manual_reconciliation` | The canonical window-renderer scenario manual mirrors the executable spec. | DOC/MANUAL CURRENT `df30337b6b1`; no execution evidence |
| `resolved_image_opacity_cache` | One resolved-resource opacity classification preserves opaque and repeated translucent image pixels. | INTEGRATED `7fa1a11ff3c`; STATIC/PERF-EVIDENCE-HELD |
| `home_pending_address` | An admitted Home action publishes the pending Home address instead of an abandoned draft. | INTEGRATED `764bc1bdfa6`; STATIC/EVIDENCE-HELD |
| `tls_failure_classification` | Stable TLS failure classes preserve committed browser state and avoid platform-detail leakage. | SOURCE/SPEC/MANUAL INTEGRATED `25b8f352e72`; deployed target unverified |
| `eval_error_side_effects` | Storage and cookie writes before a JavaScript error remain committed and origin-partitioned. | INTEGRATED `f44a0122b91`; STATIC/EVIDENCE-HELD |
| `unsupported_link_target` | Unsupported popup/new-context targets fail closed without coercing navigation into the current document. | INTEGRATED `f0a222d8695`; STATIC/EVIDENCE-HELD |
| `revision_qualified_ui_ids` | Replaced documents reject stale link, button, input, and textarea UI identities. | INTEGRATED `93e8716bcd5`; STATIC/EVIDENCE-HELD |
| `fetch_body_single_consumer` | Fetch response text, JSON, blob, and array-buffer readers share one immutable consumed bit. | INTEGRATED `7574cd2e1a8`; STATIC/EVIDENCE-HELD |
| `fixed_position` | Replacement work is active on exact base `9aad7768ebe`; rejected `98ec2f997eb` conflates style state, duplicates layout dispatch, and collapses auto/zero z-index paint semantics. | ACTIVE / UNCOMMITTED / RED |
| `animation_lifecycle` | `47df593f600` transfers identity by path, cannot represent animation lists, loses time precision, can retain unbounded stale tasks, and lacks cancel/restart/detach controls. | REJECTED / DO NOT MERGE / RED |
| `cookie_authority` | Renewable renderer authority violates one-use consumption; the distinct protocol repair did not converge. | `921fd1` REJECTED/P0; protocol STOPPED/UNCOMMITTED |
| `D3` | Held DOM-route work omits current InputEvent payload routing, crosses a Lane-2 owner, and requires ABI-aware replay rather than a local type edit. | STOPPED / UNCOMMITTED / current-origin unsafe |
| `iframe_sandbox_boundary` | Design requires document base/origin/frame generation, broker-owned frame authority, and frame-bound request/navigation schema; hidden `srcdoc` recursion has no child runtime, scripts, navigation, or input. | DESIGN GO ONLY / IMPLEMENTATION RED |
| `stage4_admission` | No provenance-qualified current full pure-Simple CLI is admitted. | NONE; no runtime/docgen/performance claim |

Root remains merge owner and final reviewer. No row changes HTML/CSS inventory
counts or supplies target-runtime, docgen, numeric performance, aggregate
HTML/CSS, full-browser, or goal PASS.

## Cookie-name token admission (2026-07-31)

| Lane | Owner | Requirement trace | Executable evidence | Manual evidence | Status |
| --- | --- | --- | --- | --- | --- |
| `cookie_name_token` | Lane F — broker network, TLS, cookies, and sandbox | REQ-WEB-BROWSER-011, REQ-WEB-BROWSER-013, REQ-WEB-BROWSER-021 | `test/03_system/app/browser/feature/browser_cookie_name_token_spec.spl` | `doc/06_spec/03_system/app/browser/feature/browser_cookie_name_token_spec.md` | IMPLEMENTED / STATIC-ONLY |

The network and script producers must converge on one ASCII token predicate in
`cookie_policy.validate_set_cookie`, before prefix checks. The exact protected
control is `sid=control`; a rejected malformed name must be absent from both
script-visible and request-header state. Root remains merge owner and final
reviewer. Runtime, docgen, and bootstrap evidence are explicitly out of scope
for this bounded lane.

## Production browser batch 26 reconciliation (2026-07-31)

Exact repository HEAD: `13273726363`.

| Lane | Result | Status |
| --- | --- | --- |
| `stop_partial_focus` | Stop preserves the partial document's focused `draft` input and byte selection through hosted chrome and isolated authority while retiring transient chrome and capability state. | INTEGRATED `a106bc48114`; STATIC/EVIDENCE-HELD |
| `cors_unsafe_header_preflight` | Unsafe author headers force a single OPTIONS preflight with sorted `Access-Control-Request-Headers`; denied policy prevents the actual cross-origin request. | INTEGRATED `bf7dfff029a`; STATIC/EVIDENCE-HELD |
| `fixed_position` | Shared out-of-flow dispatcher, transformed padding containing block, clip ownership, and one forward Draw IR/reverse-hit order are frozen below; rejected `c3cb635fca2` is not a base. | DESIGN FROZEN / IMPLEMENTATION RED |
| `stage4_admission` | No provenance-qualified current full pure-Simple CLI is admitted. | NONE; no runtime/docgen/performance claim |

The Stop and CORS executable specs/manuals are source evidence only until the
admitted pure-Simple runner and docgen lane execute them. Rejected animation
lifecycle `47df593f600`, renewable-authority `921fd1`, and stopped D3 work are
unchanged and must not be promoted. Root remains merge owner and final reviewer.

## Fixed-position recovery lanes (2026-07-31)

<!-- codex-design -->

Shared names are frozen before sidecars: `Style.position_fixed`,
`Style.transform_containing_block`, `Style.z_index_auto`,
`CssCoordinateValue`, `Transform2DSpec`, `UsedTransform2D`,
`simple_web_is_out_of_flow_positioned`, `_layout_formatting_context`,
`layout_out_of_flow_positioned_children`, `PositionedContainingBlock`,
`_fixed_containing_block`, `resolve_positioned_used_box`, and
`simple_web_stacking_paint_order`. Transform parsing may not mutate insets,
size, or `position_relative`; containing-block search starts at the parent and
the node's own transform resolves only after inset layout. The four
manual steps and helpers are frozen in the detail design and system-test plan.

| Lane | Owner/boundary | Deliverable | Status |
| --- | --- | --- | --- |
| FP-A formatting audit | Codex Spark if exposed, otherwise a small available sidecar; read-only | Enumerate every block/flex/grid/table consumption site and every duplicate positioned-child branch against the shared predicate/dispatcher | READY |
| FP-B order/clip audit | Codex Spark if exposed, otherwise a small available sidecar; read-only | Enumerate Draw IR, hit, scroll, transform-CB, inset-unit, and clip consumers; report any folded transform/inset or private order/clip derivation | READY |
| FP-C implementation | One normal-capability owner in an isolated current-origin worktree | Minimal source change using only the frozen owners; no second document pass or private painter | BLOCKED ON FP-A/FP-B REVIEW |
| FP-D SSpec/manual | Separate small sidecar after FP-C compiles | One modern four-step spec plus exact mirrored manual; fail-fast helpers until real geometry/Draw IR/pixel/hit assertions exist | BLOCKED ON FP-C |
| Merge and acceptance | Root merge owner; best available normal/highest-capability final reviewer | Review source semantics and generated-manual quality, then run each admitted pure-Simple gate once | RED |

No lane may push. Runtime, docgen, bootstrap, aggregate HTML/CSS, or production
PASS is not claimed by this design recovery.

## Reviewed browser hardening reconciliation (2026-07-31)

This is an additive current-state ledger. It does not alter earlier rejected,
stopped, RED, or evidence-held history.

| Lane | Reviewed result | Status |
|---|---|---|
| `dom_identity_generation` | The atomic generation-qualified index/route migration, rejected-eval rollback, and stale worker authority cleanup are integrated through `2155e6a31fc`. | STATIC REVIEW PASS; runtime/NFR/10,000-cycle receipt HELD |
| `disabled_ui_dispatch` | `fbecc67eb77` rejects disabled text controls before shared dispatch. | STATIC REVIEW PASS; qualified execution HELD |
| `animation_keyframe_perf` | `f57d9bc4600` and `782477146a9` skip unused layout keys and retain empty final keys. | STATIC REVIEW PASS / PERF-EVIDENCE-HELD; lifecycle and multi-list RED |
| `hosted_form_action` | `c91fdc0e67b` binds redirects to host-owned form-action authorization and conservatively rejects unauthorized navigation. | STATIC REVIEW PASS; qualified execution HELD |
| `cors_unsafe_header_preflight` | `69839e5aac3` + `cf7fce828fd` + `259d69fc010` add `FetchCorsPreflightPlan` and one broker-owned OPTIONS-to-actual transition with no preflight side effects. | STATIC REVIEW PASS; direct `HostedWebContentSession` CORS and live execution remain RED |
| `tls_mixed_content` | TLS and mixed-content source controls are present. | SOURCE PRESENT / LIVE EVIDENCE HELD |

The reviewed gap stack `be08f84be5c` + `1d16db5e149` + `dc55d6dffde` +
`ca91c19d7f8` is STATIC REVIEW PASS only for supported `N`/`Npx`, duplicate,
`initial`, `unset`, and default-parent-inherit gap winners. Nonzero `inherit`,
`revert-layer`, and qualified execution remain RED.

### Renderer-only staged CORS contract

`HostedBrowserRendererProcess` is the sole network terminal owner. It stages
only `network_job_phase` and `network_job_actual_request` beside the existing
job state, clears the completed OPTIONS handle before starting the actual
request, and reuses the command's absolute deadline. OPTIONS never finalizes a
Fetch response, follows redirects, writes renderer protocol, stores cookies or
cache entries, or seeds HSTS. `HostedWebContentSession` remains unchanged and
cross-origin-rejected until its separate BrowserSession-owned cookie and
credentials split has a reviewed contract. Executable evidence is
`test/03_system/security/browser_hosted_cors_preflight_spec.spl`; its manual is
`doc/06_spec/03_system/security/browser_hosted_cors_preflight_spec.md`.

### Reviewed browser batch (2026-07-31)

| Lane | Evidence | Status |
|---|---|---|
| Worker Reload ownership | `760a77723c7` + `1083d698021` + `1488c04d53e` reject raw worker Reload and preserve full history/index/render state. | STATIC REVIEW PASS; qualified execution HELD |
| SimpleScript replacement cancellation | `7fe6d9f68aa` stops copied same-tick callbacks after document generation changes and preserves red DrawIR/Engine2D output. | STATIC REVIEW PASS; CSS animation lists/lifecycle events remain RED |
| Iframe DrawIR tranche | `65ac7eaefe9` + `df4fdb8c6a7` + `10404d86286` embed inert `srcdoc` batches with bounded IDs/clips/order/hits and fail-closed isolation placeholders. | STATIC REVIEW PASS; legacy pixel caller migration, child runtime authority, and qualified parity remain RED |
