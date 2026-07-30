# Simple Web Browser Engine Production Hardening — System Test Plan

## Claim boundary

This plan proves the selected bounded interactive profile. Existing unit and
derived-WPT suites are supporting evidence; they do not independently prove
the production browser, sandbox, HTTPS, live events, or GC/performance targets.

## Executable specifications

1. `test/03_system/app/browser/feature/simple_web_browser_engine_production_hardening_spec.spl`
   - production HTML/CSS/Draw IR;
   - script/animation clock;
   - page events/forms;
   - browser chrome/navigation.
2. `test/03_system/security/simple_web_browser_engine_security_spec.spl`
   - HTTPS/HSTS;
   - origin/CORS/CSP/mixed content;
   - cookies/storage;
   - schemes, Node/native denial, sandbox, IPC/limits/crash.
3. `test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl`
   - startup/render/frame/input;
   - RSS, GC, lifecycle, soak, cancellation;
   - hot-path and regression budgets.
4. `test/01_unit/lib/gc_async_mut/gpu/browser_engine/fetch_deadline_spec.spl`
   - one absolute Fetch deadline across local HTTP/HTTPS redirects;
   - deterministic within-budget, aggregate-timeout, and redirect-limit cases.

Mirrored manuals use the same paths below `doc/06_spec/`.

## Manual-visible steps

- Launch the production Simple browser
- Open the conformance page
- Render HTML and CSS through canonical Draw IR
- Run JavaScript and advance the browser clock
- Operate page controls
- Operate browser navigation controls
- Navigate through verified HTTPS
- Reject hostile origin and scheme requests
- Reject renderer host capability access
- Close the page and reclaim browser resources
- Measure production browser budgets

## Feature traceability

Each row has a normal (`N`), edge (`E`), and denial/error (`D`) case.

| Requirement | Executable spec | Cases | Required evidence |
|---|---|---|---|
| REQ-WEB-BROWSER-001 canonical path | production | PATH-N/E/D | binary identity, import/route receipt, no fallback |
| REQ-WEB-BROWSER-002 HTML | production | HTML-N/E/D | DOM snapshot, visible text, malformed recovery |
| REQ-WEB-BROWSER-003 CSS | production | CSS-N/E/D | computed style, layout, reference pixels |
| REQ-WEB-BROWSER-004 Draw IR | production | DRAW-N/E/D | serialized composition, Engine2D receipt, pixels |
| REQ-WEB-BROWSER-005 script profile | production/security | JS-N/E/D | DOM mutation, explicit unsupported error, no fake success |
| REQ-WEB-BROWSER-006 one clock | production | CLOCK-N/E/D | timer/rAF/CSS frames, cancel, deterministic timestamps |
| REQ-WEB-BROWSER-007 DOM/events | production | EVENT-N/E/D | stable IDs, exact phase trace, stale target |
| REQ-WEB-BROWSER-008 controls/a11y | production | CONTROL-N/E/D | UI access focus/value/role/actions and pixels |
| REQ-WEB-BROWSER-009 chrome/nav | production | NAV-N/E/D | address/history/stop/reload/home/bookmark receipts |
| REQ-WEB-BROWSER-010 URL/Fetch | security | FETCH-N/E/D | URL/origin/redirect/abort/MIME protocol trace |
| REQ-WEB-BROWSER-011 HTTPS/HSTS | security | TLS-N/E/D | trusted success, invalid cert matrix, no fallback |
| REQ-WEB-BROWSER-012 origin/CSP | security | ORIGIN-N/E/D | same-origin success, CORS/CSP/mixed denials |
| REQ-WEB-BROWSER-013 cookies/storage | security | STATE-N/E/D | two-origin partition, attribute rules, expiry |
| REQ-WEB-BROWSER-014 sandbox/broker | security | SANDBOX-N/E/D | syscall denial, typed broker success, startup failure |
| REQ-WEB-BROWSER-015 schemes | security | SCHEME-N/E/D | http/https/about success, exact file grant, denial matrix |
| REQ-WEB-BROWSER-016 no Node/native | security | CAP-N/E/D | globals absent, FFI/process/socket/file denied |
| REQ-WEB-BROWSER-017 limits | security/perf | LIMIT-N/E/D | below-limit success, exact limit, over-limit kill |
| REQ-WEB-BROWSER-018 lifecycle | perf | LIFE-N/E/D | cancel/close/restart counts and retained-resource plateau |
| REQ-WEB-BROWSER-019 corpora/fuzz | security | CORPUS-N/E/D | pinned manifest, unsupported list, retained reproducer |
| REQ-WEB-BROWSER-020 diagnostics | all | DIAG-N/E/D | typed safe diagnostics and secret/path redaction |
| REQ-WEB-BROWSER-021 SSpec/manual | all | MANUAL-N/E/D | executable paths, mirrored docs, no stubs/placeholder passes |

The focused Fetch deadline spec supplies `FETCH-DEADLINE-N/E/D` supporting
evidence for REQ-WEB-BROWSER-010 and REQ-WEB-BROWSER-017. Its virtual monotonic
clock models local hop latency without sleeps or live network access. It proves
deadline propagation and no cache commit after timeout; it does not replace the
blocked live platform-TLS certificate/HSTS evidence.

Blocking DNS is excluded from the aggregate elapsed-time claim. The current
DNS facade accepts only a hostname, not the remaining absolute deadline; H1
checks the shared deadline immediately after lookup, but cannot interrupt the
lookup itself.

## NFR traceability

| Requirement | Executable spec | Cases |
|---|---|---|
| NFR-WEB-BROWSER-001 startup | budget | START-WARM/COLD/FAIL |
| NFR-WEB-BROWSER-002 first render/navigation | budget | RENDER-LOCAL/NAV/ERROR |
| NFR-WEB-BROWSER-003 frame pacing | budget | FRAME-CHANGED/UNCHANGED/STALL |
| NFR-WEB-BROWSER-004 input latency | budget | INPUT-POINTER/KEYBOARD/SCROLL |
| NFR-WEB-BROWSER-005 RSS | budget | RSS-WARM/60M/LIMIT |
| NFR-WEB-BROWSER-006 soak retention | budget | SOAK-WARM/10K/PLATEAU |
| NFR-WEB-BROWSER-007 GC pause | budget | GC-P50/P95/P99 |
| NFR-WEB-BROWSER-008 lifecycle reclaim | budget | RECLAIM-NAV/CLOSE/CANCEL |
| NFR-WEB-BROWSER-009 cancellation | production/budget | CANCEL-TIME/LATE/IDEMPOTENT |
| NFR-WEB-BROWSER-010 crash containment | security | CRASH-RENDERER/OTHER-SITE/PROFILE |
| NFR-WEB-BROWSER-011 security matrix | security | SECURITY-LINUX/MACOS/WINDOWS |
| NFR-WEB-BROWSER-012 conformance | security/production | WPT-CLAIM/PASS/UNSUPPORTED |
| NFR-WEB-BROWSER-013 fuzz | security | FUZZ-BUDGET/REPRO/NO-BYPASS |
| NFR-WEB-BROWSER-014 stability | budget | STABILITY-10K/STATE/RSS |
| NFR-WEB-BROWSER-015 regression | budget | REGRESS-BASELINE/DELTA/BLOCK |
| NFR-WEB-BROWSER-016 hot path | budget | HOT-NO-SPAWN/NO-RECREATE/READBACK |
| NFR-WEB-BROWSER-017 verify cap | all | VERIFY-ONCE/CYCLE-CAP/REPORT |

## Supporting evidence to retain

- tokenizer/tree-builder hardening specs;
- CSS cascade/variables and pinned derived-WPT specs;
- BrowserSession script/history/control specs;
- Draw IR and Engine2D specs;
- generic platform TLS and sandbox unit tests.

Supporting evidence is linked from the three production specs but does not
replace their live assertions.

| Verified supporting check | Result | Narrow claim only |
| --- | --- | --- |
| `sh scripts/build/build_simple_runtime_sffi.shs` | PASS | runtime TLS provider builds and stages |
| `cargo test --offline -p simple-runtime --lib --features runtime-tls 'value::net::platform_trust_tests::platform_verifier_initializes' -- --exact` | PASS | platform verifier initializes |
| `cargo test --offline -p simple-runtime --lib --features runtime-tls 'value::net::browser_http_job_tests::silent_tls_peer_respects_job_deadline_and_retires_slot' -- --exact` | PASS | TLS deadline and slot retirement |
| `sh scripts/check/check-runtime-https-openssl.shs` | PASS | `rt_tls_client_*` address+SNI OpenSSL trusted/mismatch/untrusted/stall/reset/trickle |
| `node scripts/check/check-web-render-backend-chromium-sandbox.js` | PASS | mocked Chromium-helper contract |
| `CRB_HTML="$PWD/test/09_baselines/web_html_input/vanillastyle_demo.html" timeout 60 xvfb-run -a tools/electron-shell/node_modules/.bin/electron --no-sandbox tools/web-render-backend/chromium_event_check.js` | PASS | trusted Electron form events only |
| `CRB_HTML="$PWD/test/09_baselines/web_html_input/vanillastyle_demo.html" timeout 60 xvfb-run -a /home/ormastes/dev/pub/simple/tools/electron-shell/node_modules/.bin/electron --no-sandbox tools/web-render-backend/chromium_event_check.js` | PASS | pinned Electron/Chromium injected-JS rAF and CSS keyframes changed captured pixels |
| `cargo test --offline --manifest-path src/compiler_rust/runtime/Cargo.toml --lib --no-default-features public_address_policy_rejects_any_mixed_resolution_set` | PASS | mixed-resolution egress policy unit |
| `sh test/01_unit/runtime/run_process_piped_write_test.shs` | PASS | current runtime `rt_browser_renderer_spawn_sandboxed` preinit plus `rt_browser_renderer_sandbox_enter` second-stage path: environment/cwd/inherited-FD sanitization and Landlock/seccomp/rlimit containment/limits only |

These checks do not prove a live HTTPS certificate matrix, hosted
`rt_browser_http_job`, a live HTTPS `BrowserSession`, SimpleScript, WebIR,
DrawIR, Engine2D, an admitted hosted renderer artifact, broker/CSP enforcement,
Electron, or Chromium process sandboxing. They do not promote any TLS or
SANDBOX production row.

## Held bundle status (2026-07-30)

| Held patch | Location | Review state | Executable state |
| --- | --- | --- | --- |
| DrawIR canonical oracle | `/tmp/simple-drawir-canonical-oracle.VBRqIv` | static + phase-2 manual + high review PASS | blocked |
| Content-visibility GPU guard | `/tmp/simple-content-visibility-gpu-guard-20260730` | static + phase-2 manual + high review PASS | blocked |
| Address bound | `/tmp/simple-address-bound.Qw0wSt/worktree` | static + phase-2 manual + high review PASS | blocked |
| EventLoop idle drain | `/tmp/simple-eventloop-idle-drain` | HOLD/FAIL: vacuous future timer, no perf discriminator, stale tick wording; review/docgen cycle cap | do not merge |

All remain unmerged. Exact resume: use an admitted current pure-Simple full CLI
and run each focused spec once. Seed and bootstrap output are not substitutes.
Root Codex is merge owner and final reviewer. This table changes no production
phase or acceptance-criterion status.

## False-green repairs

Before reuse, `test/03_system/gui/browser_interaction_spec.spl` must fail when
`evidence.env` is missing and must replace noncanonical matchers. Validator-
fixture JSON, wrapper provenance, QEMU boot/font smokes, and screenshots without
structured interaction are not production browser evidence.

## Evidence paths

- Renderer-process scenarios require `HOSTED_WM_ARTIFACT` and its admitted
  `HOSTED_WM_ARTIFACT_SHA256` from
  `scripts/check/check-linux-hosted-wm-live-window-evidence.shs`. The spec
  hashes the exact native `src/os/hosted/hosted_entry.spl` artifact before
  launch; it does not accept `bin/simple` or silently substitute a worker.
  The same receipt now binds the exact loaded runtime bytes by path, SHA-256,
  content identity, artifact digest, and inherited fd. This lane remains
  blocked until that provider also has trusted production build provenance;
  canonical-bootstrap absence still leaves copied-bootstrap identity unknown.
  See
  `doc/08_tracking/bug/hosted_wm_runtime_dso_unadmitted_security_evidence_2026-07-29.md`.
- text/HTML/protocol/exec/log/artifact:
  `build/test-artifacts/<spec-relative-path>/`
- GUI images:
  `doc/06_spec/image/<spec-relative-path>/`
- generated manuals:
  `doc/06_spec/<spec-relative-path>.md`

## Platform matrix

| Platform | Required claim | Current design status |
|---|---|---|
| Linux x86_64 hosted native | full live PASS | required first |
| macOS arm64 hosted native | full live PASS before macOS claim | host required |
| Windows x86_64 hosted native | full live PASS before Windows claim | host required |
| SimpleOS x86_64/aarch64 QEMU | smoke/emulated only | cannot prove hosted sandbox/TLS |
| headless CPU/validator | supporting only | cannot prove production UI/sandbox |

Every row records target, runtime/binary hash, mode, renderer/backend,
native/emulated, status/reason, exact command, artifact hash, and timestamp.
Unavailable rows remain blocked or unsupported and do not count as PASS.

## Gate order

1. focused source checks and unit/integration specs;
2. production user-flow spec;
3. security/TLS/sandbox spec;
4. native budget/GC/soak spec;
5. pinned conformance/fuzz dependencies;
6. applicable compiler/lib/UI/whole-release and environment-facade gates.

Each final unchanged green command is recorded once.

## Event and conformance evidence contracts

`scripts/check/check-wm-browser-event-routing-evidence.shs` admits the canonical
Aetheric proof before launching its Electron event probe. A positive launch
uses the pinned Electron executable with Chromium sandboxing and GPU defaults
enabled. `ELECTRON_DISABLE_SANDBOX` or
`WM_BROWSER_EVENT_ROUTING_DIAGNOSTIC_FLAGS` makes the result blocked;
diagnostic execution cannot become production PASS evidence.

Launch configuration alone is not evidence. The renderer reports the
Electron-supported `process.sandboxed` signal through an isolated preload, and
the main process records `app.getGPUFeatureStatus()`. The validator requires
`renderer_sandboxed=true`, `gpu_compositing=enabled`, and `webgl=enabled`;
missing, software, unavailable, or tampered values fail the receipt.

The event receipt joins the admitted Aetheric pixel artifact SHA-256,
Simple readback source, renderer producer, pixel count, and pixel checksum to
the existing Simple composition artifact SHA-256 and live event/frame
correlation. It does not claim BrowserSession provenance unless a canonical
producer emits and validates that field.

REQ-WEB-BROWSER-019/NFR-WEB-BROWSER-012 use the manifest, unsupported ledger,
and receipt schema under `test/fixtures/browser/conformance/`. The manifest
pins WPT and Test262 but records `status=not-run` and zero claimed cases. The
ledger remains visible and blocked; the receipt file is a schema, not a
fabricated run. Validate these invariants without downloading either suite:

```bash
sh scripts/check/check-simple-web-browser-conformance-contract.shs
```

## External PNG evidence (2026-07-29)

The focused scenario must prove a real broker HSTS include-subdomains upgrade
does not consume the redirect budget, strict PNG admission, `SBRF5` resource
round-trip, canonical Draw-IR/Engine2D absolute pixels, and no-HSTS/CSP
rejection. Runtime execution remains unclaimed while the known target compiler
blocker prevents the pure-Simple test binary from running.

## CSS URL background evidence (2026-07-29)

The hosted renderer policy scenario uses the frozen flow:

1. `Load inline and linked CSS background images through the broker`
2. `Apply background size position repeat origin and clip`
3. `Render the background image behind element content`
4. `Block background images denied by CSP or mixed-content policy`

It must retain two decoded document images but carry only the visible image in
the `SBRF5` frame, preserve redirect count `20` across the broker HSTS upgrade,
and assert exact pixels for transparent PNG-over-color, repeat/position/clip,
content paint order, and border overlay. The negative controls require a
mixed-content denial without HSTS and no queued image under `img-src 'none'`.
Animation remains enabled and unchanged. Multiple image layers and local
background attachment remain fail-closed follow-ups rather than PASS claims.

The requirement-traced fixed-background scenario was authored before its
implementation. Its pre-fix RED is source-semantic, not an observed runtime
run: `_html_draw_ir_background_image_command` rejected every attachment other
than `scroll`, so the first required `fixed_background_image` command was
absent. The known unhealthy pure-Simple runtime prevents executing that RED.
The retained oracle requires viewport tile origin `(0,0)`, element clip
`x=3,width=4`, tile origin staying at `y=0` while document scroll moves the
element shape to `y=-1`, distinct fixed/scroll repeat phase pixels, a no-repeat
fallback pixel, and an explicit `local` unsupported result.

## Canonical Draw IR semantic tree evidence (2026-07-29)

The REQ-WEB-BROWSER-003/004 system scenario is ordered:

1. assert stable element command IDs and DOM-derived `parent_id`;
2. assert the overflow-hidden ancestor clip on the top positioned child;
3. assert computed z-index metadata and stable bottom/middle/top command order;
4. round-trip the composition through the hosted SBRF encode/decode gate and
   assert semantic parentage survives;
5. replay the same composition through Engine2D and assert exact overlap colors.

This is the semantic oracle before raster evidence, not a second web IR. The
pre-fix RED was `parent_id=""` on every HTML command. The central lowering now
links main commands to their DOM parent and synthetic image/input commands to
their owning element. Draw IR v2 SDN already carries the field, so protocol
coverage removes only the stale validator rejection and retains canonical
encode/decode equality. Parent IDs remain non-authoritative metadata: Engine2D
does not use them for geometry, resources, or command dispatch. Runtime PASS
remains blocked by the unhealthy pure-Simple target.

## Post-load hardening evidence (2026-07-29)

Frozen scenario steps:

1. `Introduce a background image from JavaScript after load`
2. `Fetch the image through the existing broker policy`
3. `Render the image without resetting animation time`
4. `Cancel a late image response after Stop or navigation`
5. `Drain due GC timers without rebuilding the queue`
6. `Deliver Stop after a partial renderer write`
7. `Connect IPv6 HTTPS with a bare transport host`
8. `Deny broker robust-list disclosure from the site renderer`

Coverage must prove JavaScript and Simple Script additions use
`_start_image_source`, CSP denial queues no request, prefetched resources do
not refetch, late responses cannot mutate stopped/navigated state, and commit
does not change animation epochs. Timer checks require direct removal/update
rather than queue reconstruction. Broker/worker checks require idempotent
deferred Stop and draining a coalesced buffered frame. Transport checks keep
`[::1]` as URL authority but pass `::1` to socket/TLS, while malformed forms
remain unchanged. Native containment must observe `get_robust_list` denial
after final sandbox entry.

Current evidence is limited to focused host C containment/TLS PASS.
Pure-Simple scenarios and manual generation remain compiler-blocked. Signal
exit 139, source inspection, bootstrap output, and Rust-seed execution cannot
satisfy the runtime gate.

## Convergence evidence (2026-07-29)

Focused checks must retain:

1. exact rounded-corner background pixels, no second mask allocation, and
   fail-closed behavior after aggregate CSS-background command area consumes
   one framebuffer;
2. no Draw IR for an `opacity: 0` element or descendant; fractional subtree
   opacity stays an explicitly documented incomplete case;
3. one persisted bookmark toggle becoming the same revisioned snapshot in the
   primary renderer, an existing secondary renderer, and a newly admitted one;
4. address edit then Escape restoring `about:network` before a commit and the
   committed HTTPS URL afterward, in both primary and secondary lanes;
5. bracketed IPv6 retained in URL/origin/history while both HTTP job owners pass
   the same bare validated literal to socket/TLS;
6. a resize burst retaining only the newest deferred dimensions, and one
   document serialization per animation frame.

These remain focused source/unit/pixel gates until the pure-Simple target can
run; full bootstrap and Rust-seed output are not substitutes.

## Forced HTML line-break TDD slice (2026-07-29)

Frozen step: `Render forced HTML line breaks through canonical Draw IR`.

The modern system scenario must first prove ordered text/`br`/text semantics,
then computed `display:inline` and exact line geometry, and only then Engine2D
software pixel divergence from a single-line control. The implementation may
change only the shared tag default and inline-flow layout branch: it must not
add a parser, WebIR, renderer, cache, or animation exception.

The pre-fix RED is source-semantic because `<br>` currently enters block layout
and contributes an extra one-pixel block. Runtime execution remains blocked by
the deployed pure-Simple signal-139 failure; full bootstrap and Rust-seed
execution are prohibited substitutes.

## Retained-render TDD matrix (2026-07-29)

Before product edits, extend the existing modern `std.spec.*` specs at
`test/03_system/app/browser/feature/simple_web_browser_engine_production_hardening_spec.spl`,
`test/01_unit/os/hosted/hosted_browser_renderer_worker_spec.spl` and
`test/05_perf/browser/simple_web_browser_engine_production_budget_spec.spl`.
The system scenario owns the user-visible changed/unchanged-frame flow, the
worker spec is the deterministic counter/invalidation gate, and the perf spec
remains fail-fast until real production timing/RSS receipts exist.

| Scenario | Required counter delta |
|---|---|
| identical `advance` with no due visual work | reuse +1; serialize/parse/CSS/style/layout/paint +0; composition revision unchanged |
| timer/JS/Simple Script DOM or title mutation | parse/CSS/style/layout/paint +1 |
| committed stylesheet or navigation | parse/CSS/style/layout/paint +1; old retained counts replaced |
| decoded image replacement | paint +1; parse/CSS/style/layout +0 |
| viewport resize | CSS/style/layout/paint +1; parse +0 |
| active CSS animation frame | style/layout/paint +1; parse/CSS +0 |
| scroll or caret/selection overlay | paint +1; parse/CSS/style/layout +0 |
| repeated navigation/replacement | retained node/style/box/command counts plateau at current-document bounds |
| explicit worker-session close | all retained counts, hit index, and image revision list equal zero |

Implementation status (2026-07-29): the identical-advance and explicit-close
rows are implemented in source through one worker-owned
`SimpleWebRenderSession`; execution is runtime-blocked. The mutation,
stylesheet, image, viewport, active-animation, scroll/overlay, and repeated
replacement rows remain RED/open and must be implemented with exact
stage-selective counters before any PASS claim.

The revision/lifecycle prerequisite is also implemented in source:
render-visible image binding add, decoded replacement, failure removal, prune,
and document replacement advance `resource_revision`; active/stopped
stylesheet finalization advances `style_revision`.
`render_snapshot_since` compares all three revisions while serializing HTML
only for document/style changes. Focused tests require successful image
completion and failed-image removal to invalidate resources, late linked CSS
to invalidate the first frame, and worker close to clear the real
BrowserSession DOM/source/history, image/binding, request/load, runtime/timer,
and override owners. This is functional invalidation evidence, not
NFR-WEB-BROWSER-003 timing/RSS evidence.

Selective invalidation source status (2026-07-29): the modern system scenario
and focused worker spec now assert the entire table above, including a
dedicated title-only full-stage invalidation whose Draw IR checksum remains
stable, out-of-band image-pixel repaint whose Draw IR checksum remains stable,
changed viewport/animation/scroll/caret checksums, four exact retained-count
replacement plateaus, and close-to-zero. The renderer retains the existing
canonical nodes/rules/base styles/raw layout/composition and shares the normal
Draw IR composition tail; it adds no parser, WebIR, renderer, or pixel cache.
Execution remains RED/unavailable because the deployed pure-Simple runtime is
unhealthy. Static counter assertions are not release performance evidence.
Draw IR checksums are requested lazily by tests and cached by composition
revision; the production render path never serializes or hashes Draw IR solely
to populate evidence.

Use frozen steps `Reuse parsed layout work across unchanged animation frames`
and `Close the page and reclaim browser resources`, with
`_check_budget_row`/`_check_resource_reclaimed`. Assertions read counters from
the real `SimpleWebRenderSession`; file-content searches and placeholder
passes are forbidden. The system scenario must compare the actual frame
composition revision/checksum before and after its mutation, animation,
scroll, and unchanged steps. The production budget scenarios keep their current
`fail("NFR-WEB-BROWSER-001..017: ... not implemented")` until one healthy
pure-Simple target produces changed/unchanged latency, allocation, RSS, and
10,000-cycle receipts.

Two-layer CSS checks now require both BrowserSession resources, back-to-front
Draw-IR order, front-over-back Engine2D pixels, and atomic absence for CSP,
missing-resource, malformed, and more-than-two cases. The material-witness
unit oracle compares dense visible/offscreen counts, hashes, and Draw-IR command
counts. Runtime-provider shell self-tests cover explicit hash admission,
bootstrap-content denial, private staging, and fd-bound launch, but the
production row remains RED until trusted provider build provenance exists.
