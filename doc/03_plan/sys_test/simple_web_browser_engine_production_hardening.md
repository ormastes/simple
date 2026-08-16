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
5. `test/03_system/security/browser_tls_ipv6_service_identity_spec.spl`
   - bracketed IPv6 URL/HTTP authority separated from the bare numeric TLS
     connect and certificate service identity;
   - malformed bracket forms and ordinary DNS names stay outside the literal
     fast path;
   - offline target preparation only, not live certificate/provider evidence.

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

The focused IPv6 service-identity spec supplies `TLS-IPV6-N/E/D` supporting
evidence for REQ-WEB-BROWSER-010 and REQ-WEB-BROWSER-011. It proves the H1
owner retains `[IPv6]` for URL/HTTP authority but sends bare `IPv6` as both the
numeric transport target and TLS peer identity. It rejects malformed bracket
forms and suppresses a caller-supplied Host field. It does not replace live
platform trust, chain, expiry, SAN/IP identity, deadline, or cleanup evidence.

Blocking DNS is excluded from the aggregate elapsed-time claim. The current
DNS facade accepts only a hostname, not the remaining absolute deadline; H1
checks the shared deadline immediately after lookup, but cannot interrupt the
lookup itself.

## NFR traceability

| Requirement | Executable spec | Cases |
|---|---|---|
| NFR-WEB-BROWSER-001 startup | budget | START-WARM/COLD/FAIL |
| NFR-WEB-BROWSER-002 first render/navigation | budget | RENDER-LOCAL/NAV/ERROR |
| NFR-WEB-BROWSER-003 frame pacing | budget | ANIMATION-CLOCK-PIXELS supporting; FRAME-P95/FPS fail-closed |
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
| `sh scripts/check/check-browser-renderer-sandbox-seccomp.shs` | PASS | real `rt_browser_renderer_sandbox_enter` jail: allow-listed read/write work, non-allow-listed `socket()` is SIGSYS-killed by `SECCOMP_RET_KILL_PROCESS`. Native C-runtime evidence only; promotes no production row |
| `CRB_HTML="$PWD/test/09_baselines/web_html_input/vanillastyle_demo.html" timeout 60 xvfb-run -a tools/electron-shell/node_modules/.bin/electron --no-sandbox tools/web-render-backend/chromium_event_check.js` | PASS | trusted Electron form events only |
| `CRB_HTML="$PWD/test/09_baselines/web_html_input/vanillastyle_demo.html" timeout 60 xvfb-run -a /home/ormastes/dev/pub/simple/tools/electron-shell/node_modules/.bin/electron --no-sandbox tools/web-render-backend/chromium_event_check.js` | PASS | pinned Electron/Chromium injected-JS rAF and CSS keyframes changed captured pixels |
| `cargo test --offline --manifest-path src/compiler_rust/runtime/Cargo.toml --lib --no-default-features public_address_policy_rejects_any_mixed_resolution_set` | PASS | mixed-resolution egress policy unit |
| `sh test/01_unit/runtime/run_process_piped_write_test.shs` | PASS | current runtime `rt_browser_renderer_spawn_sandboxed` preinit plus `rt_browser_renderer_sandbox_enter` second-stage path: environment/cwd/inherited-FD sanitization and Landlock/seccomp/rlimit containment/limits only |

These checks do not prove a live HTTPS certificate matrix, hosted
`rt_browser_http_job`, a live HTTPS `BrowserSession`, SimpleScript, WebIR,
DrawIR, Engine2D, an admitted hosted renderer artifact, broker/CSP enforcement,
Electron, or Chromium process sandboxing. They do not promote any TLS or
SANDBOX production row.

## REQ-WEB-BROWSER-014 sandbox/broker — system coverage (2026-08-16)

`test/03_system/browser_engine/browser_renderer_sandbox_spec.spl` is the
step-based SSpec system scenario for SANDBOX-N/E/D; the mirrored manual is
`doc/06_spec/03_system/browser_engine/browser_renderer_sandbox_spec.md`. It
drives `scripts/check/check-browser-renderer-sandbox-seccomp.shs`.

That gate exists because the native self-check
`src/runtime/test/rt_browser_renderer_seccomp_allowlist_selfcheck.c` — added
2026-08-15 with the seccomp ALLOW-list fix — was invoked by **nothing**: no
runner, no spec, no wrapper. The jail's strongest evidence was unreachable from
any gate. The gate is fail-closed: a kernel without seccomp/Landlock and a host
without a C compiler both yield `ERROR — nothing was checked` (exit 2), never a
pass.

Status split, deliberately:

- The **gate** ran on this host: `PASS — 3 check(s) verified`, including a real
  `SIGSYS` kill on `socket()`. This is native C-runtime evidence for the jail.
- The **SSpec scenario has not executed**: no admitted pure-Simple self-hosted
  runtime exists on this host, and Rust-seed output is not evidence for this
  lane. REQ-WEB-BROWSER-014 therefore stays **not promoted**; the spec is
  written to run unchanged once a qualified runtime is deployed.

Problems 2 and 3 of
`doc/08_tracking/bug/browser_seccomp_denylist_and_inprocess_unjailed_2026-08-15.md`
(no namespace/privilege drop; in-process browsers under `src/app/browser/**`
still evaluate page script unjailed) remain open and are **not** covered by this
spec. It asserts the jail's syscall contract, not that every browser surface
enters the jail.

## Held bundle status (2026-07-30)

| Held patch | Location | Review state | Executable state |
| --- | --- | --- | --- |
| DrawIR canonical oracle | `/tmp/simple-drawir-canonical-oracle.VBRqIv` | static + phase-2 manual + high review PASS | blocked |
| Content-visibility GPU guard | current change | O(N) shared-state source + exact CPU/DrawIR/Engine2D/presented-pixel evidence + final high review PASS | execution HELD |
| Address bound | `/tmp/simple-address-bound.Qw0wSt/worktree` | static + phase-2 manual + high review PASS | blocked |
| EventLoop idle drain | `/tmp/simple-eventloop-idle-drain` | HOLD/FAIL: vacuous future timer, no perf discriminator, stale tick wording; review/docgen cycle cap | do not merge |

All remain unmerged. Exact resume: use an admitted current pure-Simple full CLI
and run each focused spec once. Seed and bootstrap output are not substitutes.
Root Codex is merge owner and final reviewer. This table changes no production
phase or acceptance-criterion status.

## Open JS animation retention blocker (2026-07-30)

| Surface | Current state | Required evidence | SPipe state |
| --- | --- | --- | --- |
| JS rAF body replacement | The minimal 1+2*3 bridge costs 7 objects/replacement: frame 4,681 is accepted at 32,767 retained objects and frame 4,682 is rejected at 32,774; `JsInterpreter.set_object_property` scans monotonically growing fresh-key storage, making the path Theta(frames^2) | Scoped tracing-GC prerequisite; retained detached-element/callback/listener identity; 256-frame live-count plateau at current+explicit roots; N/2N elapsed <=2.2x and report-only RSS receipt until a selected numeric NFR threshold; navigation/close reclaim | RED design only; do not mark REQ-WEB-BROWSER-005, REQ-WEB-BROWSER-006, REQ-WEB-BROWSER-018, NFR-WEB-BROWSER-005, NFR-WEB-BROWSER-006, NFR-WEB-BROWSER-008, or NFR-WEB-BROWSER-014 complete |

Tracked detail: `doc/08_tracking/bug/js_vm_dom_bridge_retention_quadratic_2026-07-30.md`.
Bridge-generation deletion, ID reuse, counter reset, and per-mutation runtime
rebuild are unsafe because escaped detached elements, closures, listeners, and
timers retain JavaScript identity. The diagnosis/design passed high-capability
review; Root Codex remains merge owner. This is an open blocker, not a
production claim.

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

Current evidence includes the focused offline H1 IPv6 service-identity SSpec
and focused host C containment/TLS PASS. The SSpec proves target preparation
and wire authority, not a live connection or certificate result. Qualified
pure-Simple execution and manual generation remain compiler-blocked. Signal
exit 139, source inspection, bootstrap output, and Rust-seed execution cannot
satisfy the runtime gate.

## Convergence evidence (2026-07-29)

Focused checks must retain:

1. exact rounded-corner background pixels, no second mask allocation, and
   fail-closed behavior after aggregate CSS-background command area consumes
   one framebuffer;
2. no Draw IR for an `opacity: 0` element or descendant; fractional subtree
   opacity stays RED until
   `browser_css_opacity_subtree_draw_ir_spec.spl` proves these four visible
   steps:
   `Compute inherited subtree opacity`,
   `Emit one composited Draw IR group`,
   `Render through canonical Engine2D`, and
   `Verify source-over pixels`.
   With alpha byte `(pct * 255 + 50) / 100` and premultiplied source-over
   rounding `(x + 127) / 255`, three separate fixtures must yield:
   `0xFFFF7F7F` for a parent-only red box in one 50% group over white,
   `0xFF7F7FFF` for an opaque blue child fully covering its red parent inside
   one 50% group, and `0xFFBFBFFF` for a blue box at 50% inside a same-bounds
   transparent/no-paint parent at 50%, over white. In that nested fixture only
   blue has effective 25% alpha.
   The scenario also requires one opaque HTML root and one child reference at
   the exact parent paint slot. Hostile fixtures must reject an unknown child
   target, a child referenced by two group commands, duplicate/orphan/cyclic
   IDs, depth 513, aggregate command 1,025, aggregate batch 1,026, encoded
   payload 1,048,577 bytes, and clipped command-plus-group pixel work above
   `viewport_pixels * 16`, all before transient allocation. A
   `filter: opacity(...)` control must not emit a CSS-opacity group;
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

Animation evidence split (2026-07-30): the budget spec now has one supporting
modern SSpec scenario with four visible steps. It advances CSS and JavaScript
from the same renderer timestamp, requires the rAF callback to observe exactly
`16` ms, and requires a changed composition revision. Its Draw-IR oracle binds
the `stage` rectangle to `(0,0)`, `32x24`, and exact red/blue colors before one
persistent `Engine2dCompositorBackend` must produce exactly 768 corresponding
pixels with zero skipped commands. A title-only revision cannot satisfy those
checks. This remains a deterministic clock/Draw-IR/pixel oracle, not
NFR-WEB-BROWSER-003 performance evidence. The adjacent p95/FPS and
RSS/GC/10,000-cycle scenarios call the existing production fixture and budget
helpers, then fail with requirement-specific missing-receipt errors. They
remain RED until an admitted source-matched production artifact supplies real
samples and provenance.

Two-layer CSS checks now require both BrowserSession resources, back-to-front
Draw-IR order, front-over-back Engine2D pixels, and atomic absence for CSP,
missing-resource, malformed, and more-than-two cases. The material-witness
unit oracle compares dense visible/offscreen counts, hashes, and Draw-IR command
counts. Runtime-provider shell self-tests cover explicit hash admission,
bootstrap-content denial, private staging, and fd-bound launch, but the
production row remains RED until trusted provider build provenance exists.

## Batch-2 held and RED evidence (2026-07-30)

- `details_summary_rendering_spec.spl` is a held, unexecuted modern SSpec with
  the original four-step disclosure/event scenario plus a marker scenario with
  the exact steps `Parse the authored disclosure summary`, `Resolve the default
  disclosure marker state`, `Emit canonical disclosure marker Draw IR`, and
  `Render exact closed and open Engine2D pixels`. The marker stays on the O(N)
  Web semantic/layout path and lowers as canonical Draw IR text. Explicit
  `display:list-item` survives the fast declaration dispatcher and retains the
  marker/slot, while author `display:block` suppresses both; executable status
  remains RED pending an admitted current pure-Simple full CLI.
- `browser_invalid_form_method_spec.spl` holds the final-reviewed production,
  modern SSpec, and canonical phase-2 manual behavior: invalid or empty form
  and submitter method tokens normalize to GET, POST remains POST, and
  unsupported `dialog` remains rejected. It is held and unexecuted pending an
  admitted current pure-Simple full CLI.
- No `maxlength` regression is planned: accepting a valid leading digit
  sequence is the required parser behavior, so the rejected candidate is not a
  bug or coverage gap.
- `overflow: clip` remains RED. Its future SSpec must distinguish origin,
  importance, `@layer` order, specificity, source order, shorthand/longhand,
  and CSS-wide values before asserting clip-without-scroll-container pixels.
  Existing flattened-rule evidence cannot prove that contract.
- History API parent evidence is implemented statically and execution-held.
  Its protocol SSpec sends the bounded complete ledger plus current index and
  random SBR2 capability, then proves atomic rejection of unknown,
  reordered, oversized, out-of-range, origin-mismatched, or
  capability-mismatched state. A current/back/forward neighbor tuple is not
  accepted as authority.
- Primary renderer close-retry is HOLD/FAIL at the three-review cap. Fatal poll
  can revoke authority inside an already-entered block, after which
  `begin_resize` lacks a fresh authority check and may call the closed/failed
  renderer. The remaining lifecycle work reviewed sound, but the patch has no
  accepted manual, executable PASS, merge, or production status.
- Fractional animation is HOLD/FAIL at the three-review cap for two blockers:
  invalid longhand/shorthand tail declarations erase the earlier valid winner
  instead of selecting the last valid declaration (`2; -1` computes default 1,
  and an invalid shorthand wipes its predecessor); and unchecked i64
  subtraction remains in reconcile (`current - old.start`, `current -
  old.paused`) and apply (`animation_time - start`). The next SSpec must prove
  last-valid cascade selection plus saturating subtraction at i64-min and both
  timestamp boundaries. The f64, negative-zero, fractional, zero, infinite,
  fill, exact-color, and checked-add work reviewed sound but remains unpromoted,
  unmerged, and unexecuted.

## Cascade provenance and overflow-clip RED contract (2026-07-30)

Status: **PROPOSED / UNIMPLEMENTED**.

Create
`test/03_system/feature/web_platform/css/cascade_provenance_overflow_clip_spec.spl`
only with the frozen visible steps `Collect declaration provenance`, `Select
cascade winners`, `Resolve CSS-wide values`, and `Render overflow clip pixels`.
Use `_setup_cascade_provenance_document`,
`_check_declaration_provenance`, `_check_cascade_winners`,
`_check_css_wide_values`, and `_check_overflow_clip_pixels`; until production
exists, each checker must call
`fail("RED: cascade provenance and overflow clip are unimplemented")`.

The four steps must prove, respectively:

- admitted declarations retain user-agent/author/animation origin, importance,
  named/anonymous/nested/reopened/predeclared layer identity and order,
  each layer's implicit outer sublayer, applicable document-global conditional
  registration,
  encapsulation context, element-attached style rank, matched specificity, and
  per-declaration source order across wrappers, presentational hints,
  stylesheet rules, inline style, and animation samples; the reserved user and
  transition ranks plus nonzero encapsulation contexts must be rejected as
  unsupported in the admitted light-DOM profile;
- normal layers, reversed important layers, unlayered declarations, inline
  declarations, invalid tails, shorthand/longhand collisions, and animation
  below author-important select the exact property winner. Controls prove
  normal top-level implicit-outer `revert-layer` exposes the last explicit
  layer, non-attached important implicit-outer `revert-layer` falls to the
  next origin, important element-attached `revert-layer` exposes important
  style-rule declarations, and a false conditional layer does not register;
- inherited and non-inherited properties resolve `initial`, `inherit`, `unset`,
  `revert`, and `revert-layer` only after cascade selection from a retained
  lower-candidate stack, including lower layer and lower origin fallback.
  Author `revert` must remove animation-origin candidates as well as author
  candidates;
- `overflow: clip` and `hidden` produce exact canonical Engine2D clip pixels,
  while only `hidden`, `auto`, and `scroll` expose scroll-container behavior.
  Exact controls assert `(Visible, Hidden)` computes to `(Auto, Hidden)` and
  `(Clip, Scroll)` to `(Hidden, Scroll)`; root pair propagation and HTML-body
  fallback preserve computed state, make the source element used pair
  `Visible`, and map viewport used `Visible`/`Clip` to `Auto`/`Hidden`;
  replaced computed `Hidden` has used `Clip`; default clip pixels use the
  padding box at zero `overflow-clip-margin`; `Clip` creates neither BFC nor
  programmatic scroll while `Hidden` does. Unsupported boundary rows stay RED
  rather than being omitted.

Fold these exact controls under the four visible steps; they are not extra
manual steps:

| Control | Required result |
| --- | --- |
| `@layer low { #t { overflow:hidden } } #t { overflow:revert-layer }` | computed `Hidden` from `low` |
| direct normal `Clip` plus child-layer normal `Hidden` inside one parent layer | direct implicit-outer `Clip` wins |
| direct important `Clip` plus child-layer important `Hidden` inside one parent layer | child-layer `Hidden` wins |
| false conditional declares `middle`, then applicable `late` registers before `middle` reopens | `middle` registers later and wins normal precedence |
| same sheet after viewport makes the earlier `middle` condition true | registry/ranks rebuild; `middle` registers before `late`, so `late` wins normal precedence |
| resize leaves every document-global condition unchanged; element-sensitive wrapper contains `@layer` | registry/ranks are reused; element-sensitive layer registration rejects as unsupported |
| unlayered style-rule `overflow:revert-layer!important` over author-normal `Hidden`, with no explicit important candidate | user-agent `Visible`, not author-normal `Hidden` |
| inline `overflow:revert-layer!important` over style-rule `overflow:hidden!important` | style-rule `Hidden` |
| author `overflow:revert!important` plus sampled animation `overflow:hidden` | user-agent `Visible`; animation is removed |
| descendant toggles `.hot` under `article:has(.hot)` | the candidate `article` ancestor is invalidated and recomputed |
| child insert/reorder changes `:first-child`/`:nth-child` and an ancestor class changes a descendant selector | affected sibling/child cohort and dependent descendants are invalidated; unrelated branch cache remains hit |
| computed pairs `(Visible, Hidden)` and `(Clip, Scroll)` | `(Auto, Hidden)` and `(Hidden, Scroll)` |
| HTML root pair not both `Visible`; then root pair both `Visible` with first body pair | viewport uses root in the first case and body in the second; propagation source used pair is `Visible`; viewport maps `Visible`/`Clip` to `Auto`/`Hidden` |
| replaced `Hidden`, non-replaced `Clip`, and `Clip` with omitted clip margin | replaced computed/used are `Hidden`/`Clip`; `Clip` cannot programmatically scroll or create a BFC; exact clip edge is padding-box + `0px` |

The performance row requires one realistic layered fixture to report
stylesheet parse, matched candidates, declarations visited, occupied bands,
cache hits/misses, invalidated nodes, elapsed time, and max RSS. Acceptance is
O(N) cascade work, where N is candidate rules plus matched declarations, with
precomputed band ranks, `occupied_bands <= matched_declarations`, and traversal
of occupied bands only—no per-node dense global-layer scan, candidate sort,
declaration-text concatenation, or per-frame static-rule reparse. A
viewport/condition truth flip must show registry/rank rebuild; unchanged truth
must show reuse. This design cites
<https://www.w3.org/TR/css-cascade-5/> and
<https://www.w3.org/TR/css-overflow-3/>; it creates no production claim.

## Bookmark title persistence SSpec (IMPLEMENTED STATIC / EXECUTION HELD)

Target the existing modern scenario at
`test/03_system/app/browser/feature/simple_web_browser_engine_production_hardening_spec.spl`.
The generated manual must expose exactly these four steps:

1. `Open bounded titled documents through hosted chrome`
2. `Commit bookmarks through the parent profile owner`
3. `Restart the renderer generation and profile-backed window`
4. `List persisted bookmarks with safe titles`

The setup creates two canonical HTTPS documents. One title is exactly 512
UTF-8 bytes, including a multibyte boundary; the other is 513 bytes. Step 2
must traverse the real parent Favorite release and profile transaction, not
call `BrowserSession.add_favorite` directly. Step 3 performs a site-swap
generation replacement and then closes and reopens the profile-backed window.

The in-process parity branch uses the existing H1 mock registry and only
`HostedWebContentRegistry` public actions: create with a file-backed
`BrowserBookmarkStore`, advance the window, focus/type/submit the address,
advance to consume the mock response, release Favorite, close, then construct a
new registry from the same profile path. It must not read or mutate
`registry.sessions[*].browser` and must not call any BrowserSession Favorite
method. The reopened registry's parent-owned `profile_bookmarks` is compared
with the sandbox production snapshot inside the same four visible steps.

Required assertions use built-in matchers only:

- the admitted 512-byte title persists byte-for-byte beside the unchanged
  canonical URL;
- the 513-byte title is not persisted and its restored UI bookmark label is
  the canonical URL fallback;
- both restored bookmark nodes retain the correct `href`, add/remove remains
  canonical-URL based, and no duplicate row appears;
- an `SBRF8` title with stale generation, stale reply ID, wrong current URL,
  NUL, or an encoded 513-byte payload cannot update the parent's latest title;
- title lengths above 684, noncanonical base64, checked-offset overflow or
  truncation, and encoded-plus-decoded title work exceeding the remaining
  1 MiB frame/Draw-IR budget reject before decoded-title allocation;
- a forged, syntactically valid SBRF8 carrying a 513-byte decoded title rejects
  before title decode/admission without using the trusted frame encoder;
- an injected post-mutation canonical snapshot-read failure rolls back the
  SQLite row/title and leaves parent revision/UI snapshot and restart state
  unchanged;
- legacy `SBRF7` renders with no title witness and cannot reuse a prior
  generation's title.

The original RED was the hosted `(url, url)` persistence call: even the valid
512-byte document title becomes the URL in both the sandbox parent and
`HostedWebContentRegistry` reconciliation. Source inspection or direct
BrowserSession-only coverage cannot promote this scenario. No bootstrap or
Rust-seed result is admissible.

## Rejected plan gates (HOLD/FAIL)

- Hosted HTTPS reached the three-review cap: HSTS belongs to the broker, not
  the worker, and renderer launch must unset `LD_LIBRARY_PATH`.
- Parent history now uses canonical `SBRHJ1`: `O/-` is omitted, `N/-` is
  JavaScript null, and `V/<canonical-base64>` is an explicit value, including
  zero-length base64 for empty. The focused SSpec must prove empty `V`
  preserves the committed fragment.

All other reviewed aspects are sound but unpromoted. Hosted HTTPS remains the
failed design in this subsection; history is superseded by the canonical
static contract below and still has no executable production claim.

## Parent-owned History API ledger SSpec (IMPLEMENTED STATIC / EXECUTION HELD)

Target
`test/03_system/security/browser_parent_history_ledger_spec.spl` and its
mirrored manual. Expose exactly these four steps:

1. `Stage parent history authority`
2. `Accept one capability-bound history proposal`
3. `Reject hostile or stale history proposals`
4. `Preserve chrome across renderer failure`

Use `make_history_process_fixture` and `expect_history_public_state`.

The folded controls cover pushState, replaceState, back, forward, site swap,
and generation restart. They distinguish omitted, null, and explicit empty
URL wire forms; the empty-string case starts at
`https://history.test/app?q=1#kept` and must retain `#kept`. Public chrome
evidence asserts the parent current URL, back URL, forward URL, index, complete
ledger, and unchanged state after stale generation/reply, wrong committed URL,
wrong SBR2 capability, cross-origin resolution, reordered/unknown/non-neighbor
entries, malformed lengths/base64, index errors, entry 65, and payload
overflow. No private renderer ledger or direct runtime symbol is admissible.

Static/manual completion remains HELD until one source-matched pure-Simple
full CLI runs the focused SSpec and docgen once.

## Held SimpleScript listener evidence

Status: **STATIC/MANUAL/FINAL-REVIEW PASS; UNEXECUTED / UNMERGED**.

The bundle at `/tmp/simple-simple-script-events.5IEatF` repairs the prior
vacuous system claim by loading SimpleScript `listen` declarations through
`BrowserSession` and invoking only canonical `dispatch_dom_event`; it does not
use `inject_dom_event`. Its phase-2 manual is `complete 1/1`, `stubs 0/1`, with
exactly four visible steps:

1. `Register exact capture and bubble listeners`
2. `Dispatch click capture then bubble then input and change`
3. `Apply one checkbox default action`
4. `Lower the mutated box through canonical Draw IR and Engine2D`

Folded assertions prove target/event/action UTF-8 maxima `2048`, `64`, and
`4096` bytes and reject `2049`, `65`, and `4097`; accept 256 live listeners,
reject listener 257, normalize `onclick` identity without growing the set, and
reuse a removed slot. Missing targets, unsupported actions, `on*` attribute
actions, and malformed capture reject. Dispatch preserves pipe-bearing text
and attribute actions, runs armed/clicked/input/change in exact order, rebinds
executor roots after checkbox and navigation mutations, performs one checkbox
default, and totals seven listener callbacks. Canonical rendering proves
initial red `0xFFEF4444` present/blue `0xFF2563EB` absent, then red absent/blue
present with changed full pixels.

No executable claim exists until an admitted current full pure-Simple CLI runs
the focused modern SSpec once.

## Primary navigation chrome cancellation gate

The fresh repair in `/tmp/simple-web-pointer-safe` makes
`HostedBrowserRendererProcess` the primary page-pointer owner. The focused
modern policy scenarios must prove the press wire, the exact pointer-up wire
before chrome ownership, a redundant no-op, resource-job retention, and retry
with the original event ID. The hosted-entry source gate additionally requires
the primary chrome route to call `cancel_pointer` before arming the control and
the poll route to flush retained cancellation before lower-priority sync work.

Execution and docgen remain held until an admitted current full pure-Simple CLI
is available. Static/manual review cannot promote this row to production PASS.

## Renderer command capability SSpec (IMPLEMENTED STATIC / EXECUTION RED)
The focused modern scenario is
`test/03_system/security/browser_renderer_command_capability_spec.spl`. Its
mirrored generated manual must expose exactly these four steps:

1. `Admit the trusted capability owner`
2. `Issue one fresh command token`
3. `Reject an unissued command token`
4. `Retire all capability material`

Frozen setup/checker names are
`setup_trusted_capability_owner_fixture`,
`check_trusted_capability_owner_admitted`,
`check_fresh_command_token_issued`,
`check_unissued_command_token_rejected`, and
`check_all_capability_material_retired`. Commit `879f28bc059` integrates the
production graph plus source/manual scenarios. Runtime and 10,000-cycle
receipts remain RED; future incomplete replacement helpers must fail
explicitly.

The fixture launches a bounded fake renderer through the real piped hosted
process boundary. One mode writes `ready` and a future frame in one write for
the ready-buffer check. A second controlled mode uses a test-only FIFO path
embedded in its generated executable: after writing `ready`, it waits for the
harness release byte, writes the future frame, acknowledges that write through
the FIFO, and still has not read renderer stdin. Only after that acknowledgement
does the parent issue `init`, making the separate-read ordering deterministic
without sleeps. A conforming mode reads the complete init payload and tail,
echoes its tuple, and proves an accepted nonblank Draw-IR/Engine2D result.

Required assertions use built-in matchers only:

- `ready` plus retained bytes rejects as `unexpected-ready-buffer`;
- a future reply delivered in a separate read, with the expected numeric IDs
  but without the issued capability, rejects as
  `unissued-renderer-reply`;
- a deterministic split write stages the host tuple, writes payload plus only
  31 capability bytes, and proves a matching staged capability is
  inadmissible; only the final byte moves all staged fields to issued fields;
- rejection occurs before network policy, cookie mutation, HTTP-job start,
  frame decode, history/title mutation, retained-image replacement, or active
  state transition;
- failure cleanup leaves state `failed`, command capability empty, root request
  ID zero, pending wire empty, command deadline zero, network handle zero,
  deferred commands empty, and retained image resources empty; the bounded
  fake child closes successfully;
- restart rejects the prior tuple first as `stale-generation`; the old
  capability paired with the new generation rejects as
  `unissued-renderer-reply`;
- uppercase, short, long, nonhex, empty, and `-` command capabilities reject;
  exactly 32 lowercase hexadecimal bytes are accepted;
- application payload `1,048,544` plus a 32-byte capability is accepted;
  payload `1,048,545` plus 32 rejects without allocation; the total decoder
  buffer never exceeds `256 + 1,048,576 + 8,192`;
- generation/root/wire/reply IDs accept canonical
  `1..9223372036854775806`; zero is ready-root-only, and signs, leading zeroes,
  `9223372036854775807`, textual max-plus-one, and checked-increment overflow
  reject before state mutation;
- legacy `SBR1` and legacy fetch/frame/network schemas reject in both hosted
  production directions;
- page, SimpleScript, JavaScript, common-codec, and worker paths cannot install,
  replace, consume, or inspect the parent's staged or issued tuple; formatting
  arbitrary 32-byte hexadecimal text grants no authority;
- codec and worker do not own or import the private parent creator; deterministic
  evidence drives the parent creator/conversion unchanged-state error path,
  while production entropy uses only `crypto_sffi.random_hex(16)` with no
  fallback, fault switch, alternate RNG, or raw runtime shortcut;
- the conforming control reads the command, echoes generation/root ID/token
  and immediate reply ID, reaches `active`, renders exact nonblank pixels, and
  leaves the capability retired after frame acceptance;
- stop/cancel retires staged and issued capability fields but preserves the
  last admitted frame checksum/resources; close, failure, and site swap retire
  both tuples and clear retained images, pending wire, deferred commands, and
  network handle.

The deterministic parent fixture exercises empty, short, uppercase, nonhex,
and all-zero creator/conversion outcomes. Each maps to
`renderer-command-entropy-unavailable` while pending bytes, IDs, deadlines,
staged/issued tuples, network state, and counters remain unchanged. A direct
validator-only assertion cannot satisfy this evidence, and no production fault
switch is allowed.

Owner-specific executable evidence is:

Step 1 builds the real entry closure rooted at
`src/os/hosted/hosted_entry.spl` with an admitted current pure-Simple compiler.
The receipt binds the parent, common codec, worker, crypto facade, closure, and
final artifact digests. It proves one atomic SBR2 production graph with no
reachable SBR1/SBRN1/legacy frame direction or downgrade flag. Source
inspection alone does not satisfy the step.

Step 2 launches that artifact through the bounded fake renderer. One complete
host wire produces exactly one fresh token, moves it from staged to issued only
after the final byte, and accepts one correctly bound echo. The capture redacts
the token while proving canonical length/class, issue count, root/wire
correlation, and no parent mutation on entropy failure.

Step 3 drives hostile page, SimpleScript, JavaScript, common-codec, and worker
inputs. None can install or consume parent staged/issued state, and guessed,
replayed, wrong-wire, wrong-root, wrong-generation, partial-write, or
buffered-ready replies fail before broker/frame authority. A deterministic
fixture exercises the parent creator/conversion error from normal command
activation and proves malformed entropy leaves every parent field unchanged.
A direct validator-only check is insufficient. A control may format identical
bytes but cannot create the matching live issued tuple.

Step 4 consumes the legitimate echo, then covers command replacement,
stop/cancel, timeout, entropy failure, network failure, renderer failure, site
swap, close, and registry teardown. Every path leaves staged/issued/root/wire
IDs and token bytes empty; deferred commands never own token bytes. Ordinary
stop/cancel preserves the last admitted frame while terminal cleanup clears
retained images.

Fold performance evidence into step 4 without adding visible steps: 10,000
command/fetch/frame cycles report issue/failure/staged/consumed/reject
counters, bounded entropy-latency histogram, transient token allocation count,
post-warmup/final/max RSS, and command p95. Acceptance requires zero entropy
failures, zero staged/issued capability bytes after quiescence, exactly one
transient 32-byte token allocation per host wire and zero retained token
allocations, warm capability p95 <=1 ms, total input-to-paint p95 <=50 ms,
relative command latency regression <=5%, RSS <=384 MiB, and final RSS growth
<=10%. Entropy p99 is captured report-only.

The receipt also requires exactly one `crypto_sffi.random_hex(16)` call and one
transient 32-byte token allocation per installed host wire, zero entropy calls
or token allocations for deferred/rejected wires, and zero token
bytes/allocations after quiescence. Issued-tuple admission adds no subprocess,
module-string parse, or unbounded lookup.

Protocol captures pair bounded raw header bytes with decoded fields but redact
the capability value. No source inspection, direct validator-only assertion,
Rust seed, or bootstrap result may promote the row.

## Batch-3 execution ledger (2026-07-30)

- Durable Home has production/spec/canonical-manual/final-high PASS, held
  unexecuted and unmerged.
- Nonzero-clock JavaScript timers have
  production/spec/manual/final-high PASS, held unexecuted and unmerged.
- `<mark>` has production/spec high PASS but manual FAIL at the three-cycle cap
  because six bullets remain visible from helper and shutdown text.
- Text overflow remains HOLD/FAIL on unresolved CSS-wide cascade behavior.
- Iterative DOM tag search has production/spec static high PASS but manual FAIL
  at the three-cycle cap; only preorder assertions are folded.

The prior SimpleScript PASS and CSS-cascade/bookmark-title designs remain as
recorded. None of these rows is executable or merged evidence.

## Batch-5 executable and held evidence (2026-07-30)

- `browser_session_textarea_lifecycle_spec.spl` has four visible steps and
  final high review PASS at static/manual scope. It proves the shared
  CR/LF/CRLF-to-CRLF form encoder through both production serializers, exact
  focus/edit/commit event order, UTF-8 multiline POST encoding, and
  component-bound Draw IR/Engine2D pixels. Runtime status remains HELD pending
  one admitted current pure-Simple focused execution.
- Renderer fd launch, hosted navigation visibility, HTTPS terminal outcomes,
  native `<progress>`, and unchanged-frame SBRF8 reuse all remain HOLD. Their
  exact remaining defects are recorded in the agent-task plan; none may be
  cited as executable or production evidence.

## Batch-6 executable and held evidence (2026-07-30)

- Bookmark-title SBRF8 transport and atomic profile persistence have final
  static/manual review PASS. The system scenario binds the real parent Favorite
  owner and covers rollback/restart/UI parity plus forged 513-byte rejection;
  hosted execution remains HELD for an admitted artifact.
- SBR2 production activation is integrated at `879f28bc059` with the selected
  `crypto_sffi.random_hex(16)` facade wired into parent-issued causal
  authority. This is static-only; runtime and 10,000-cycle evidence remain RED.
- Negative stacking, radio lifecycle, and JavaScript property/GC prototypes
  remain HOLD at their recorded architecture boundaries and are not merged.

## Batch-7 executable and held evidence (2026-07-30)

- Address input and durable Home have final static/manual review PASS. Address
  coverage binds every hosted mutation owner to strict UTF-8/control admission
  and state-atomic rejection; Home coverage binds profile restart and both
  hosted owners. Focused execution remains HELD for an admitted pure-Simple
  artifact.
- Hosted-parent capability issuance and atomic all-direction SBR2 production
  migration are integrated at `879f28bc059`; runtime and 10,000-cycle evidence
  remain RED.
- Shared-clock, label activation, and SimpleScript listener prototypes remain
  HOLD at their exact recorded defects and are not merged.

## Generation-qualified DOM identity integrated static-held scenario

<!-- codex-design -->

Status: **STATIC EVIDENCE PRESENT / SOURCE HOLD-RED / TARGET EXECUTION HELD**. The focused
executable is
`test/03_system/app/browser/feature/browser_dom_identity_generation_spec.spl`;
its complete mirrored manual is
`doc/06_spec/03_system/app/browser/feature/browser_dom_identity_generation_spec.md`.
It traces REQ-WEB-BROWSER-004/007/008/017/018 and
NFR-WEB-BROWSER-004/005/006/008/014/015/016, but cannot promote them before
production execution.

Design-audit status: **EVIDENCE CONTRACT PRESENT; SOURCE REPAIR REQUIRED**.

The modern SSpec and mirrored manual expose exactly four steps:

1. `Build the document identity index`
2. `Dispatch through stable routes`
3. `Replace the document during a handler`
4. `Reject stale routes and release the index`

Frozen helpers are `setup_dom_identity_generation_fixture`,
`check_dom_identity_index_built`, `check_stable_route_dispatch`,
`check_document_replacement_during_handler`, and
`check_stale_routes_and_index_release`. Each now invokes production owners with
direct assertions; no placeholder PASS is present.

| Requirement | Executable/manual evidence | Static status |
| --- | --- | --- |
| REQ-WEB-BROWSER-004 | current route -> layout hit -> canonical Draw IR -> Engine2D pixels | oracle present; execution held |
| REQ-WEB-BROWSER-007 | callable, SimpleScript, UI, label/default, value/style/focus/text routes | oracle present; execution held |
| REQ-WEB-BROWSER-008 | direct/worker stale press-release cannot activate replacement; route/capability cleanup | oracle present; source HOLD/RED |
| REQ-WEB-BROWSER-017 | atomic script-publish/load/index rollback including cookie-write queue | oracle present; source HOLD/RED |
| REQ-WEB-BROWSER-018 | exact N/2N work plus versioned 10,000-cycle receipt schema | schema present; numeric receipt held |
| NFR-WEB-BROWSER-004/005/006/008/014/015/016 | p95, allocations, index lifecycle/bytes, RSS, stale/budget fields | not promoted |

Step 1 first proves `BrowserSession.new()` publishes the generation-1 blank
DOM/index pair, then builds one document with duplicate author IDs, forward external form
ownership, explicit and nested labels, same-name radios with distinct form
owners, text controls, and capture/target/bubble listeners. It asserts the
first-preorder ID winner, exact form/label/radio routes, and root-to-target
event path. It also admits canonical `id:` and `path:` layout hit keys and
rejects malformed/over-depth keys. A body fixture intersperses text,
`style`/`script`/`meta`/`link`, and layout elements at two depths. It proves
the exact `(layout_parent_route, layout_element_ordinal) -> route` relation:
only layout-element children advance the body-rooted ordinal. Counters show
exactly two bounded passes using shared
`HTML_MAX_TREE_DEPTH`/`HTML_MAX_NODES` and no recursive lookup.

Step 2 exercises pointer press/release, label forwarding, radio selection,
Space activation, text editing, focus, beforeinput/input/change/blur/focusout,
SimpleScript/JavaScript listeners, UI access, and form serialization. Every
receipt carries `DomNodeRoute`; interactive descendants do not forward,
reentrant activation does not loop, label cancellation prevents forwarding,
control cancellation rolls back pre-activation state, sibling order is
`label,control`, nested order is `label,control,label`, a frozen path does not
retarget after handler removal, and nested actions share one document-wide
budget. Radio fixtures prove an explicit no-form-owner key, never a
document-root sentinel.

The dispatch assertions distinguish page-visible author-ID projections from
typed route authority. They require typed target/current/related routes on
every production receipt and generation-owned callable, SimpleScript, and
JavaScript listeners. A script batch that changes `id`, `form`, `for`, radio
identity, or labelable structure publishes DOM/index/bridge/listeners once;
an index-build failure publishes none. Value/style/text-only mutation keeps
the generation.

Focused folded cases bind each callable listener's JS heap object to its
stored route before dispatch, require value/style/focus changes to preserve
the current index and object identity, and require child-replacing
`textContent` to advance the generation. They also exercise the exact label
orders/cancellation/rollback above and require a 4,096-callable checkbox's
synthetic input work to share the outer dispatch budget.

Step 3 replaces the document from a target handler with author and numeric IDs
resembling the old document. The handler unwinds, but old callbacks/defaults do
not query the new index and do not focus, click, select, edit, or submit the
replacement. Hosted press, pending Space, selection, UI-access targets, and
bridge listener keys clear or become stale.

Before replacement, the fixture snapshots `BrowserRuntimeState`, its route to
JS-heap-object map, callable callbacks, and the session-owned
`SimpleScriptExecutor` root/runner/index/callbacks. `BrowserSession` owns no
stateful `ScriptHost`; its ScriptHost helper is a pure candidate-DOM transform,
covered by unchanged committed DOM. Replacement proves the new DOM/generation/index and every new script
component publish together while all old-generation callbacks disappear. A
separate script-driven publish/index-staging failure proves every prior
component remains byte-for-byte/current-route identical and no candidate root,
listener, callback, generation, or pending broker cookie write escapes.

The rollback oracle drives oversized `innerHTML` plus a cookie write through
`eval_script` into `publish_dom_snapshot`, then rejects an oversized load and a
duplicate-node candidate. All retain DOM, generation/index, bridge/callable and
SimpleScript roots/callbacks, and `pending_script_cookie_writes`. The queue
assertion is currently RED and blocks source promotion.

The direct and isolated-worker fixtures retain the old layout hit key and captured generation,
then replaces the document before release. The session
`route_for_layout_target_key` gate returns `stale_target` without parsing or
new-index lookup; no release click or focus/edit reaches the replacement. The
worker must clear retained hit/pressed routes and root-command/capability state;
that cleanup oracle remains source HOLD/RED.

Step 4 submits forged old-generation routes through runtime bridge, UI access,
pointer release, keyboard activation, edit, focus, label, radio, and form
paths. Each returns `stale_target` without mutation/callback. Close then
proves zero live/retired indexes and generation-owned listeners after bounded
quiescence.

The rejection matrix is behavioral, not source-only. It sends a NUL
`route-node:` string, a bare author ID, a bare numeric/node ID, a valid
old-generation `dom-route-v1`, a stale `id:`/`path:` hit key, and a
same-generation press/release locator pair that resolves to different routes
through runtime bridge, UI access, hosted press/release, keyboard/Space,
selection/edit/focus, label/radio/form/default action, callable listeners,
SimpleScript, JavaScript, and public event creation/dispatch. Every case
returns the canonical invalid-route or `stale_target` result before callback,
mutation, focus, submission, or Draw IR work. Standards-facing
`getElementById(author_id)` remains the only author-ID lookup and returns the
first-preorder route projection; it never authorizes a host mutation.

Folded cases run the production fixture at `N` and `2N` routable elements.
Visits/allocations scale within 10%, elapsed `2N/N <= 2.2`, and repeated
author/form/label/radio queries report expected O(1) index work while
route-to-node/event-path queries report bounded O(depth) parent-chain work and
zero recursive/full-tree searches. The 10,000
replacement/dispatch receipt includes build and input-to-paint p95,
allocations, live/retired index counts/bytes, post-warmup/final/max RSS, and
stale/budget rejects. Acceptance requires input-to-paint p95 <=50 ms, RSS
<=384 MiB, retained bytes/final RSS within 10% of baseline, and no stale
callback or unreleased index.

The executable currently instantiates that versioned receipt with `-1` for
every runtime-measured field and `runtime-held` status. Those sentinels are a
fail-closed schema witness, not 10,000-cycle or NFR evidence.

Step 4 also captures canonical component-bound Draw IR and Engine2D pixels for
the surviving current control. The oracle asserts the exact current
`DomNodeRoute`, Draw IR command owner/node, and current-control inside/outside
pixels; retired routes contribute no action, command, or pixel.

Static review additionally runs an exact deletion census for
the detail-design file-by-file matrix: `be_dom_event_identity` routing and its
`node:<node_id>` fallback, event-identity-at-path,
layout-target-key, identity matching, recursive route lookup,
implicit-submit association recursion,
focus/form/default/dispatch `*_id`, NUL routes, text `BeDomEvent`/event-api
targets, ScriptHost/SimpleScript/JS bridge IDs, BrowserRuntimeState numeric DOM
IDs and separate generation, Space/selection/hosted IDs, direct load-time
`bind_dom`, UI NUL encoding, and every runtime recursive consumer. Any
production hit is RED. Renderer-only node/resource/Draw IR IDs, JS heap object
IDs, and standards-facing author-ID projections are explicit exclusions.

Behavioral author lookup proves production `getElementById` uses the O(1)
first-preorder index winner and that an element without an author ID exposes
no `node:<node_id>` projection. The implicit-submit folded case visits
controls once and reports indexed form-owner queries with no recursive
association lookup.

The executable spec uses built-in matchers and fail-fast placeholders until
production exists. Its generated manual hides setup mechanics, keeps these
four steps visible, and links typed protocol/text/performance captures. Rust
seed, bootstrap, helper-only, and source-scan evidence are inadmissible.

## Favorite mutation truth scenario

The navigation batch-9 scenario extends the existing canonical browser textual
UI-access SSpec with exactly four visible steps:

1. `Inspect Favorite before a network document is open`
2. `Attempt Favorite through the public textual action`
3. `Open a network document and add it through the same action`
4. `Remove the saved page and retain an enabled truthful control`

It invokes only `BrowserSession.ui_access_snapshot` and
`BrowserSession.ui_access_act`, proves a fresh `about:blank` session exposes a
disabled Favorite control, proves the rejected click leaves the bookmark
snapshot empty, and proves add/remove success against one canonical HTTPS
document. The page renderer does not own this parent chrome control, so this
scenario makes no Draw IR or Engine2D pixel claim. Runtime status remains HELD
until the current source has an admitted pure-Simple build receipt.

## Crash-recovery batch 10 evidence

Commit `d4ffb28dae4` adds executable modern SSpec coverage for:

- `REQ-WEB-BROWSER-017` / `NFR-WEB-BROWSER-006`: bounded timer and animation
  queues reject overflow and resume after drain;
- `REQ-WEB-BROWSER-007/008/010/021`: externally associated controls submit in
  document order while controls owned by another form do not leak;
- `REQ-WEB-BROWSER-010/011`: valid and invalid bracketed IPv6 authorities share
  canonical HTTP/parser admission;
- a forged stateless renderer reply cannot commit a pending document; and
- prior-site frame, image, and raster-cache state is gone while a real
  replacement renderer is still starting.

Each scenario has a mirrored manual and a behavioral failure discriminator.
Static diff/layout/direct-environment guards passed once. Target execution and
docgen remain HELD; the current pure-Simple interpreter crash is recorded
separately and neither bootstrap nor the Rust seed is admissible evidence.

## Batch 11 executable evidence

Commit `0d6c055a489` adds requirement-tagged behavioral coverage for:

- disabled fieldset button/text actions and the first-legend exception through
  public UI access, with unchanged callbacks, DOM state, and pixels;
- malformed HTTPS document redirects rejected with the exact error before any
  permit or provisional/pending commit state;
- a real SimpleScript timer replacing the body and producing exactly one new
  UI revision plus the next current DrawIR/hit frame; and
- current-frame-only GPU image retention, omitted-pixel release, and two
  consecutive validated reference frames.

Commit `ae4c3d56ce3` adds the focused self-hosted interpreter interpolation
SSpec and manual. Static review passed, but phase-2/3 execution did not run:
concurrent sessions owned the shared bootstrap cache and the isolated seed
probe failed delegation before checking source. No target PASS is claimed.

## Batch 12 executable evidence

Commit `8f2ae532371` adds requirement-tagged behavioral coverage for:

- a focus handler disabling its text input before `beforeinput`, with no value,
  callback, revision, or pixel mutation;
- changed, identical, and invalid address drafts through canonical textual UI
  access and revision publication;
- a stale hostile requester origin unable to read a partitioned cookie written
  by the validated active document; and
- native `blockquote` semantics, UA margins, exact Draw IR geometry, and exact
  Engine2D pixels.

Independent static review accepted all four lanes after correcting manual
parity, scenario counts, traceability accounting, and an unsupported cascade
claim. Static guards passed once. Qualified execution/docgen remain HELD:
artifact audit found no pure-Simple binary with source provenance at or after
the interpolation fix.

## Batch 13 executable evidence

Commit `9f720c62c72` adds focused modern specs and complete manuals for:

- native `header` semantics through exact Web layout, Draw IR, and Engine2D
  pixels;
- valid/malformed padding shorthand, physical, and horizontal-LTR logical
  source order, including ASCII-whitespace tokenization;
- same-size clipped fractional-opacity siblings with bounded cropped surfaces,
  plus backdrop and differing-size fail-closed cases;
- signed seconds/milliseconds and exact consecutive animation frames;
- timer-driven SimpleScript stylesheet replacement preserving an unchanged
  animation epoch while publishing one style revision; and
- Node-compatible completed timer-handle refresh admission at the shared
  capacity, explicitly outside browser reachability.

Independent adversarial reviews and one combined static guard pass succeeded.
Target execution/docgen remain HELD pending a source-admitted pure-Simple
artifact at or after `ae4c3d56ce3`.

## Batch 14 executable evidence

Commit `15b6727a5ce` adds modern executable specs and complete manuals for:

- bounded renderer title transport and canonical-URL-keyed bookmark
  persistence/reopen through the public hosted registry;
- hostile loader variables absent after the real sandboxed renderer spawn;
- canonical lexical parent lookup/assignment, escaped closure identity, and
  invalid/cyclic environment rejection as a JS reclamation prerequisite;
- chrome/page press replacement, exactly-once cancellation, and same-window
  renderer generation swap without stale release;
- last-valid animation shorthand/longhand selection, numeric time-token
  classification, saturating add/subtract boundaries, and exact
  fractional/zero/infinite/fill/paused/resumed Draw IR and Engine2D frames.

Independent review rejected and withdrew the reconstructed SimpleScript
listener bundle because current parse-local DOM IDs cannot bind a detached
frozen event path across replacement and aggregate listener/action-byte
lifecycle accounting is not yet canonical. The stronger existing O(N)
content-visibility GPU guard required no duplicate change.

Static guards passed once. Qualified execution/docgen remain HELD because the
artifact audit found no clean provenance-qualified Stage-4 full CLI at or after
the current compiler/browser commits.

## Batch 15 executable evidence

Commits `b0f47f6aac0` and `d25b474cf0f` add modern executable specs and complete
manuals for:

- a script-denying CSP that advances the shared clock and exact CSS animation
  frame while executing zero script callbacks or mutations;
- missing/empty/invalid form method GET fallback, exact valid GET/POST, and
  fail-closed `dialog`/transport behavior through public submit actions;
- identical WebIR-produced Draw IR submitted through the canonical Engine2D
  upload/comparison route, with actual software result receipt and all 2,048
  pixels checked against an absolute panel oracle;
- details/summary omitted-paragraph parsing, closed/open/missing/nested
  visibility, nearest interactive descendant precedence, preventDefault, and
  post-keyframe structural suppression; and
- document-origin-aligned rAF deadlines, nested deferral, cancellation,
  pending/completed refresh metadata, overflow-safe timer math, and a
  1,001-task `i64.max` wakeup boundary.

The same tranche reconciled the SBR2 design contract around the existing
entropy facade, common capability validator, private parent issuance, atomic
all-direction activation, and retained 1 MiB/i64/10,000-cycle gates. SBR2
production is subsequently integrated at `879f28bc059`; only static evidence is
admitted, so runtime and 10,000-cycle gates remain RED.

Independent review and one static guard pass per integration tranche succeeded.
Qualified execution/docgen remain HELD pending a clean provenance-qualified
current Stage-4 pure-Simple CLI.

## Batch 16 evidence boundary

- Broker-owned HSTS policy is pushed at `6e7b4517a81`.
- Generation-qualified DOM identity design is pushed at `ac847fbfb67` but
  remains PROPOSED/RED; no executable identity evidence is admitted.
- Crash-safe one-use SBR2 capability work is pushed at `879f28bc059`.
  Review evidence is static-only; the runtime and 10,000-cycle rows remain RED.
- Stage-4 admission is NONE because available artifacts are stale-lineage.
  Therefore no focused execution, docgen, runtime PASS, or implementation
  completion is claimed.
- JS VM reclamation evidence remains RED. A rejected candidate did not carry
  generations in external handles, did not reference-count independent escaped
  owners, and inferred numeric references instead of emitting typed mark edges.
  Generation-qualified handles, owner refcounts, and typed edges are required
  before the 1,000-dispatch/lifecycle scenarios can be admitted.
- The earlier pre-SBR2 history candidate/design remains rejected. Its
  superseding capability-bound parent ledger is integrated at `2e188a745d9`
  with static evidence only; no runtime history evidence enters this plan.

## Batch 17 evidence reconciliation

- Figure UA-margin behavior is integrated at `897368fb592`; its semantic,
  Draw IR, and pixel evidence is static/evidence-held.
- Generation-safe JS reclamation is frozen at `ef90c16b194` as
  PROPOSED/RED design only; no GC implementation or runtime evidence is
  admitted.
- Live post-listener default-action validation is integrated at
  `ca4769405d6`; evidence is static/held.
- The Stage-4 provenance and real-motion wrapper at `6c76b8ac0c0` passes its
  own self-tests, but no target runtime execution is claimed.
- Capability-bound parent history is integrated at `2e188a745d9`; evidence is
  static/held.
- Stage-4 admission remains NONE at `/tmp/simple-history-h1.d3de` and for the
  active build, which remains stale-lineage. No focused runtime, docgen,
  10,000-cycle, or full-browser PASS is admitted.
- Selected-profile `<menu>` UA spacing is pushed at `b107a4e2a9e`; its
  rendering evidence is static/held and supplies no runtime PASS.
- G2 reclamation implementation is BLOCKED with no commit. The operative
  `std.js.types` contract still uses the raw-i64 ABI and does not provide the
  required lexical-parent identity, generations, free-list state/counters,
  typed edges, or external-root ownership; the planned symbols do not match
  the repository contract. The repository-wide A-through-E migration must
  precede executable implementation.
- Generation-safe GC design `ef90c16b194` remains PROPOSED/RED. No G2
  executable evidence, goal completion, or runtime PASS is admitted.

## Batch 18 final evidence boundary

`test/03_system/security/browser_renderer_script_mime_boundary_spec.spl`
contains the integrated `2211d8ae1b5` four-step SBR2 scenario for
REQ-WEB-BROWSER-005/010/012/021:

- mixed-case, parameterized canonical JavaScript MIME admission plus classic
  non-`nosniff` compatibility;
- classic `nosniff` rejection for a non-JavaScript MIME;
- redirected module final-MIME rejection before alias/source-cache mutation;
- deterministic warning plus loader advance with no hostile body evaluation,
  cookie write, DOM marker, global side effect, or module cache publication.

The paired manual is
`doc/06_spec/03_system/security/browser_renderer_script_mime_boundary_spec.md`.
The row is STATIC/EVIDENCE-HELD, not runtime PASS.

`test/05_perf/web_render_chrome/web_gpu_paint_shape_key_scaling_spec.spl`
contains the integrated `9653a09fdea` four-step isolated scenario for
NFR-WEB-BROWSER-015/016:

- exact deterministic 4,096-op and 8,192-op `SceneCommand` fixtures;
- byte-for-byte `x,y,w,h;` ordering, repeated identity, and one-coordinate
  inequality;
- one warm construction plus exactly nine monotonic samples at each size;
- median 2N construction no greater than three times median N construction.

The paired manual is
`doc/06_spec/05_perf/web_render_chrome/web_gpu_paint_shape_key_scaling_spec.md`.
The performance row remains HELD/UNMEASURED because no admitted current
pure-Simple runtime executed it. Static source checks are not a measured
performance PASS.

Additional integrated static/evidence-held scenarios at exact repository HEAD
`9653a09fdea118b5d502fa06989d83e12cd4fe19` cover selected `<small>` UA
sizing (`b9e1a0e6707`), HSTS Back/Forward traversal (`416ccc6efb8`),
input-button keyboard activation (`e9b50343645`), and DrawIR text-transform
parity (`e7af94e921c`). JS `store_kind` remains RED design only at
`f8b926e0dd5`.

Stage-4 admission remains NONE: the active `4cdd` build is dirty/stale and
has no receipt. D1 `1728` is held locally and MUST NOT MERGE. D2 stopped
without a commit and remains pending review/unmerged. Therefore this batch
admits no runtime, docgen, 10,000-cycle, performance, full-browser, or goal
PASS.

## Batch 19 final evidence boundary

Exact repository HEAD is
`165d7b3a8c799163e99321c56d0b4310c3b79fb4`.

- `<abbr>` inline-flow and canonical text-rendering evidence is integrated at
  `8beb64585b2` and remains STATIC/EVIDENCE-HELD.
- Duplicate-offset CSS keyframe cascading is integrated at `2078c3dfab4`.
  Its unit and four-step Draw IR/Engine2D scenario/manual are static-held;
  qualified runtime execution remains unavailable.
- Attachment-navigation activation rejection is integrated at `165d7b3a8c7`
  and remains STATIC/EVIDENCE-HELD.
- Stage-4 admission is NONE. The `807182` build is dirty, divergent from
  current source, and has no provenance receipt.
- D1 and D2 remain held on lineage through `06dc5620781`; both are
  **DO NOT MERGE**. D3 remains active and uncommitted.

Existing evidence counts and RED/evidence-blocked classifications remain in
force except for the explicit `<abbr>` reclassification and animation-row
extension in the canonical HTML/CSS plan. No runtime, docgen, 10,000-cycle,
performance, full-browser, goal, or aggregate HTML/CSS PASS is admitted.

## Batch 22/23 final evidence boundary

Exact repository HEAD is
`8372ca9607fb6f6ee8fda40c19ff3f573350bbe4`.

The following integrated pairs provide source and manual evidence only:

- `test/01_unit/lib/common/web/browser_session_redirect_scheme_security_spec.spl`
  and its `doc/06_spec` mirror cover trusted request-scheme downgrade checks
  (`4a141af30d5`) and mixed-content rechecking after loopback redirects
  (`59cbfff9857`);
- `test/03_system/app/browser/feature/browser_address_selection_backspace_spec.spl`
  and its mirror cover selected-address Backspace (`5f0758db126`);
- `test/02_integration/rendering/simple_web_layout_child_index_spec.spl` and
  its mirror cover column-gap-sensitive flex wrapping (`d620217fb0c`);
- `test/01_unit/os/compositor/simple_web_window_renderer_spec.spl` and its
  mirror cover finite terminal animation artifact retention and static/timed
  cache separation (`1671c187b9f`);
- `test/03_system/app/browser/feature/browser_input_event_payload_spec.spl`
  and its mirror cover exact input payload/type dispatch through Draw IR
  (`c2013e78545`); and
- `test/03_system/app/browser/feature/browser_address_url_reference_spec.spl`
  and its mirror cover URL-reference resolution and absolute worker-wire
  publication (`8372ca9607f`).

All seven rows are STATIC/EVIDENCE-HELD. Intervening compiler, GPU, and
documentation commits are concurrent ancestry only and are neither reviewed
nor claimed here. Animation candidate `47df593f600` is REJECTED and is not in
`origin/main`; cookie authority `921fd1` remains REJECTED/P0; the distinct
cookie-authority protocol lane and D3 are STOPPED/UNCOMMITTED. The iframe
sandbox-origin/capability contract remains an architecture RED gap. Stage-4
admission is NONE, so no focused runtime, docgen, performance, 10,000-cycle,
aggregate HTML/CSS, full-browser, or goal PASS is admitted.

## Batch 24/25 final evidence boundary

Composition base is
`745e12de62dded9dab51e023e316649df2c1394f`.

The following integrated source/spec/manual pairs remain evidence-held:

- `test/03_system/feature/web_platform/css/table_formatting_spec.spl` and its
  mirror cover collapsed-border width-before-style precedence
  (`d01ff82c92a`);
- `test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.spl`
  and its mirror cover reset input discovery plus keyboard/pointer activation
  (`8ce17d741ca`);
- the canonical
  `doc/06_spec/01_unit/os/compositor/simple_web_window_renderer_spec.md` is
  reconciled at `df30337b6b1`; this manual-only change adds no execution;
- `test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_adv_spec.spl`,
  `test/03_system/os/simpleos_host_gpu_image_execution_contract_spec.spl`, and
  their mirrors cover cached opaque/translucent image classification and exact
  blend controls (`7fa1a11ff3c`);
- `test/03_system/app/browser/feature/browser_home_pending_address_spec.spl`
  and its mirror cover admitted pending Home address publication
  (`764bc1bdfa6`);
- `test/03_system/security/browser_tls_failure_preservation_spec.spl` and its
  mirror cover stable TLS errors and committed-state preservation
  (`25b8f352e72`);
- `test/03_system/app/browser/feature/browser_eval_error_side_effects_spec.spl`
  and its mirror cover origin-partitioned writes before JavaScript errors
  (`f44a0122b91`);
- `test/03_system/app/browser/feature/browser_live_default_action_spec.spl` and
  its mirror cover fail-closed unsupported link targets (`f0a222d8695`);
- `test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.spl`,
  `test/03_system/app/browser/feature/browser_focus_editability_order_spec.spl`,
  and their mirrors cover revision-qualified DOM UI identities
  (`93e8716bcd5`); and
- `test/01_unit/lib/common/web/browser_session_async_spec.spl` and its mirror
  cover one-consumer Fetch response bodies (`7574cd2e1a8`).

Fixed positioning is ACTIVE/UNCOMMITTED/RED after rejection of `98ec2f997eb`.
Animation lifecycle `47df593f600` is REJECTED/DO-NOT-MERGE for unsafe identity,
list, time, retention, and lifecycle-control behavior. Cookie authority
`921fd1` remains REJECTED/P0 and the distinct protocol repair remains
STOPPED/UNCOMMITTED. D3 is STOPPED/UNCOMMITTED and current-origin unsafe because
its typed dispatcher omits newer InputEvent payload routing and overlaps a
Lane-2 owner. Iframe is DESIGN-GO only and implementation RED until the broker
owns trusted frame identity, origin, and one-use capability state before any
child runtime.
Stage-4 admission is NONE. Therefore no target-runtime, docgen, numeric
performance, 10,000-cycle, aggregate HTML/CSS, full-browser, or goal PASS is
admitted.

## Go chrome correction cycle 1/3 (2026-07-31)

`REQ-WEB-BROWSER-009` and `REQ-WEB-BROWSER-010` trace to
`test/03_system/app/browser/feature/browser_session_ui_access_controls_spec.spl`
and its generated/manual mirror. The bounded correction covers one shared Go
activation owner, relative-reference normalization, protocol-to-worker and
direct-hosted-entry routing fixtures, accessibility order/enabled state,
width 268/312/324 clipping boundaries, and independent literal-color pixel
regions. Runtime/docgen evidence remains RED because of the pre-existing
`browser_session_runtime.spl` parse blocker; this cycle admits one static gate
only and makes no runtime PASS claim.

Cycle 2/3 replaces the direct hosted-entry source-text assertion with callable
`hosted_browser_process_activate_address` behavior shared by Go release and
address Enter. The production-process fixture checks one normalized pending
navigation, callback count, focus/error truth, and committed-history
preservation. Exact narrow-width batch deltas and literal boundary pixels now
cover command suppression at 311/312 and 323/324. The 21/21 manual remains a
hand-reviewed static candidate; runtime/bootstrap/docgen/push stay uninvoked.

Cycle 3/3 pins each clipped browser window batch to embedding rectangle
`(0,0,width,126)` with clipping enabled at widths 267, 268, 311, 312, 323,
and 324. These exact embedding assertions complement the retained command
suppression, command-count deltas, and literal boundary-pixel evidence.

## Fixed-position recovery evidence design (2026-07-31)

<!-- codex-design -->

Rejected candidate `c3cb635fca2` supplies no evidence. The future executable
path remains
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/fixed_position_rendering_spec.spl`;
its only manual path is
`doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/fixed_position_rendering_spec.md`.
The manual exposes exactly one scenario with these four steps:

1. `Build fixed-position formatting-context controls`
2. `Exclude fixed children from table and grid consumption`
3. `Resolve viewport and transformed fixed geometry and clips`
4. `Match Draw IR paint order with reverse hit traversal`

The frozen setup/checker names are
`setup_fixed_position_context_fixture`,
`check_fixed_children_out_of_flow`,
`check_fixed_containing_blocks_and_clips`, and
`check_fixed_draw_ir_hit_order`. Checkers use `expect(...).to_equal(...)`,
`to_contain`, and numeric comparisons directly; boolean-wrapper assertions,
custom matchers, empty helpers, and placeholder passes are forbidden.

| Requirement | Required deterministic oracle |
| --- | --- |
| one positioned-child owner | block/flex/grid/table fixtures show each fixed child laid out once; grid track and table cell/row geometry equal controls without the fixed child |
| fixed containing block | viewport coordinates survive scroll; nearest ancestor transform wins; transformed border-box `(40,30)` with `3px` borders yields padding-CB origin `(43,33)` and `left:5; top:6` yields `(48,39)` |
| inset used values | `20x10; right:12px; bottom:14px` resolves to `(288,216)` in `320x240`; `32x16; left:auto; right:10%; top:25%; bottom:auto` resolves to `(256,60)` while computed evidence retains auto/percent units |
| own transform | `40x20; left:20px; top:30px; translate(7px,9px)` keeps inset origin `(20,30)`, produces Draw IR/hit origin `(27,39)`, uses the viewport rather than self as fixed CB, and establishes the transformed padding CB for a nested fixed child |
| fixed clipping | viewport-fixed ignores ordinary ancestor overflow; transform-contained fixed uses that normal clip chain; nested overflow produces one admitted and one clipped Draw IR/pixel/hit point |
| stacking distinctions | negative, static with authored z, positioned auto, explicit zero, and positive controls have stable forward order; auto does not create the explicit-zero trap and zero does |
| Draw IR/hit parity | structured `DrawIrComposition` owner order is the sole forward order; reverse traversal selects its last eligible clipped owner at every overlap point |

The scenario asserts semantic style/geometry and structured Draw IR before
Engine2D readback pixels, then asserts target keys at the same inside/outside
points. Table/grid non-consumption, transformed padding geometry, nested
clip/hit behavior, right/bottom and auto/percent used coordinates, independent
own-transform geometry, and static/auto/zero controls are release-blocking; a
viewport-only happy path is insufficient. Step three's existing
`check_fixed_containing_blocks_and_clips` owns all exact inset and transform
coordinates; step four proves the resulting matrix geometry participates in
the one Draw IR/reverse-hit order.

No `.spl` or generated manual is created in this docs-only recovery. Once
implemented, run the affected spec and standalone docgen exactly once with the
admitted pure-Simple runtime, require `0 stubs`, review the four-step manual,
run the direct-environment guards, and require zero executable specs under
`doc/06_spec`. Until then, fixed positioning remains RED.

## Primary pointer compatibility suppression (2026-07-31)

Canceled primary `pointerdown` owns one cross-route compatibility rule: retain
`pointerup` and same-target `click`, but suppress the subsequent compatibility
`mousedown` and `mouseup`. The shared semantic owner is `BrowserSession`; the
in-process `HostedWebContentSession` and isolated
`HostedBrowserRendererWorkerSession` retain only the one-bit press lifetime
needed by that owner.

The production call chains are:

- `HostedWebContentSession.dispatch_pointer_at -> BrowserSession primary
  pointer compatibility owner`; and
- `HostedBrowserRendererRegistry.dispatch_pointer_at ->
  HostedBrowserRendererProcess.begin_pointer -> browser renderer protocol ->
  HostedBrowserRendererWorkerSession._dispatch_pointer -> BrowserSession
  primary pointer compatibility owner`.

| Requirement | Executable SSpec | Manual | Deterministic oracle |
|---|---|---|---|
| REQ-WEB-BROWSER-007 | `test/03_system/app/browser/feature/browser_pointer_compatibility_suppression_spec.spl` | `doc/06_spec/03_system/app/browser/feature/browser_pointer_compatibility_suppression_spec.md` | exact `pointerdown,pointerup,click,` trace; no `mousedown`/`mouseup` |
| REQ-WEB-BROWSER-008 | same | same | hosted/worker callback parity, one click, zero navigation, cleared press state |

The displayed manual uses exactly these four steps:

1. `Open the same canceling button in hosted and isolated renderers`
2. `Press the primary pointer on both buttons`
3. `Release the primary pointer over the original targets`
4. `Observe pointer click order and suppressed compatibility mouse events`

The scenario is a STATIC candidate until an admitted pure-Simple runner and
docgen lane execute it. This bounded implementation invokes neither runtime,
bootstrap, nor docgen and therefore makes no runtime PASS claim.

## Stop partial-document focus preservation (2026-07-31)

Stop terminates the current load but does not replace the admitted partial
document. Page-owned focus, text selection, input view, and caret epoch
therefore remain live state. Only pressed/chrome ownership and terminal
renderer command authority are retired. Document-replacing Back, Forward,
Reload, Home, Go, and open navigation retain their existing focus-discard
policy.

The complete production call chains are:

- `HostedWebContentSession.dispatch_chrome_pointer ->
  BrowserSession.ui_access_act -> BrowserSession.stop_loading`; and
- `HostedBrowserRendererRegistry.dispatch_chrome_pointer ->
  HostedBrowserRendererProcess.begin_stop -> capability-bound browser
  renderer protocol -> HostedBrowserRendererWorkerSession._dispatch_navigation
  -> BrowserSession.stop_loading`, followed by terminal frame admission and
  command-capability retirement.

| Requirement | Executable SSpec | Manual | Deterministic oracle |
|---|---|---|---|
| REQ-WEB-BROWSER-008 | `test/03_system/app/browser/feature/browser_stop_partial_focus_spec.spl` | `doc/06_spec/03_system/app/browser/feature/browser_stop_partial_focus_spec.md` | hosted/isolated focused target `draft` and byte selection `1..5` remain identical |
| REQ-WEB-BROWSER-009 | same | same | public hosted Stop and capability-bound isolated Stop both complete once |
| REQ-WEB-BROWSER-021 | same | same | visible partial body remains, transient chrome state clears, and isolated root/capability authority is empty |

The displayed manual uses exactly these four steps:

1. `Open the same partial document in hosted and isolated renderers`
2. `Retain page selection while transient chrome state is armed`
3. `Activate Stop through hosted chrome and isolated authority`
4. `Observe partial focus and selection with transient state retired`

The scenario is a STATIC candidate until an admitted pure-Simple runner and
docgen lane execute it. This bounded implementation invokes neither runtime,
bootstrap, nor docgen and therefore makes no runtime PASS claim.

## Space activation across modifier events (2026-07-31)

A pending button Space press belongs to the matching Space release. An
intervening non-activating Shift keydown or keyup participates in normal DOM
dispatch but must not clear that owner. The state machine remains solely in
`BrowserSession`; hosted and isolated adapters only translate their existing
key protocol into the shared owner.

The complete production call chains are:

- `HostedWebContentSession.dispatch_key_with_shift ->
  BrowserSession.dispatch_dom_keyboard_code_event -> shared keyboard
  activation state`; and
- `HostedBrowserRendererRegistry.dispatch_key_with_shift ->
  HostedBrowserRendererProcess.begin_key_with_shift -> browser renderer protocol ->
  HostedBrowserRendererWorkerSession._dispatch_key ->
  BrowserSession.dispatch_dom_keyboard_code_event -> shared keyboard
  activation state`.

| Requirement | Executable SSpec | Manual | Deterministic oracle |
|---|---|---|---|
| REQ-WEB-BROWSER-005 | `test/03_system/app/browser/feature/browser_space_modifier_activation_order_spec.spl` | `doc/06_spec/03_system/app/browser/feature/browser_space_modifier_activation_order_spec.md` | focused button stays armed from Space down through Shift down/up |
| REQ-WEB-BROWSER-007 | same | same | exact `focus,keydown,keydown,keyup,keyup,click,` trace and one click |
| REQ-WEB-BROWSER-008 | same | same | hosted/worker trace, focus, pending-state, callback, and default-state parity |

The displayed manual uses exactly these four steps:

1. `Open the same keyboard button in hosted and isolated renderers`
2. `Focus both buttons through the host Tab route`
3. `Hold Space while pressing and releasing Shift on both buttons`
4. `Release Space and observe ordered activation in both renderers`

The scenario is a STATIC candidate until an admitted pure-Simple runner and
docgen lane execute it. This bounded implementation invokes neither runtime,
bootstrap, nor docgen and therefore makes no runtime PASS claim.

## Checkable canceled-pointer focus preservation (2026-07-31)

Canceled primary `pointerdown` suppresses the pointer's implicit focus default,
not the same-target `click` or a checkbox's pre-activation/input/change
defaults. The shared `BrowserSession` click dispatcher therefore selects a
focus-preserving DOM default-action policy only while completing that canceled
primary-pointer stream. Existing programmatic and keyboard click callers keep
their prior focus policy.

The complete production call chains are:

- `HostedWebContentSession.dispatch_pointer_at -> BrowserSession primary
  pointer completion -> focus-preserving DOM default action`; and
- `HostedBrowserRendererRegistry.dispatch_pointer_at ->
  HostedBrowserRendererProcess.begin_pointer -> browser renderer protocol ->
  HostedBrowserRendererWorkerSession._dispatch_pointer -> BrowserSession
  primary pointer completion -> focus-preserving DOM default action`.

| Requirement | Executable SSpec | Manual | Deterministic oracle |
|---|---|---|---|
| REQ-WEB-BROWSER-007 | `test/03_system/app/browser/feature/browser_checkable_canceled_pointer_focus_spec.spl` | `doc/06_spec/03_system/app/browser/feature/browser_checkable_canceled_pointer_focus_spec.md` | exact `focus,pointerdown,click,input,change,` trace; no blur/focusout |
| REQ-WEB-BROWSER-008 | same | same | hosted/worker focused target `keep`, checked checkbox, and five callbacks |

The displayed manual uses exactly these four steps:

1. `Open the same text input and checkbox in hosted and isolated renderers`
2. `Focus both text inputs through the primary pointer`
3. `Activate both checkboxes after canceling their pointerdown events`
4. `Observe checkable order and preserved text focus`

The scenario is a STATIC candidate until an admitted pure-Simple runner and
docgen lane execute it. This bounded implementation invokes neither runtime,
bootstrap, nor docgen and therefore makes no runtime PASS claim.

## Sandboxed `srcdoc` child authority (RED, 2026-07-31)

The current iframe path is renderer-only recursion, not a child `BrowserSession`
document.  The following scenario is required before child script, request,
navigation, or input may be enabled. It binds one
`BrowserChildIdentity(parent_dom_generation, iframe_route,
child_frame_generation)`. Child document URL is `about:srcdoc`; fallback and
effective base are distinct URL fields; security identity is typed `Origin`.
`HostedBrowserRendererProcess.generation` remains only the outer SBR2 process
generation. The isolated trusted ledger is `HostedBrowserRendererProcess`;
worker `BrowserSession` is a mirror. Direct `HostedWebContentSession` uses the
shared session broker and makes no SBR2 claim.

| Requirement | Executable SSpec | Manual | Deterministic oracle |
|---|---|---|---|
| REQ-WEB-BROWSER-003/004/014 | `test/03_system/security/browser_iframe_sandbox_contract_spec.spl` | `doc/06_spec/03_system/security/browser_iframe_sandbox_contract_spec.md` | typed identity/base/origin and iframe+CSP sandbox admission; two opaque siblings differ |
| REQ-WEB-BROWSER-005/007/008/010/012/013 | same | same | script, fetch/navigation, cookie/storage, and input validate identity/policy before mutation and consume one permit |
| REQ-WEB-BROWSER-018/019/021 | same | same | malformed/oversized/unknown/forged/replayed/stale cases retire cleanly; direct/isolated parity and current manual |

The displayed manual uses exactly these four steps:

1. `Create the sandboxed srcdoc child document`
2. `Broker one child script operation`
3. `Constrain child request navigation and input`
4. `Revoke stale child authority`

The frozen helpers are `setup_iframe_sandbox_contract_fixture`,
`check_child_document_context`, `check_child_script_broker_use`,
`check_child_request_navigation_input`, and
`check_child_revocation_and_stale_rejection`. They require absent/empty
sandbox, CSP intersection, malformed/oversized/unknown tokens, two opaque
siblings, forged identity rejection-before-mutation, and hosted/isolated parity.
They also distinguish outer per-hop SBR2 from inner per-child `SBCP1`, and
prove direct mode uses no wire. A validator-only check, source scan, Rust seed,
or bootstrap result cannot promote this RED row. It remains static until one
admitted pure-Simple focused execution and docgen produce the manual.

## Reviewed hosted/rendering batch (2026-07-31)

| Requirement area | Evidence | Status |
|---|---|---|
| Worker Reload broker ownership | Raw worker Reload evidence in `browser_ui_access_controls_spec.spl` rejects before mutation and preserves URL/loading/pending/full history/index/body/DrawIR. | STATIC REVIEW PASS; qualified execution HELD |
| Same-tick SimpleScript replacement | The BrowserSession animation integration evidence stops callbacks copied from the old generation after body replacement, with red DrawIR/Engine2D retained. | STATIC REVIEW PASS; animation lists/lifecycle events RED |
| Renderer staged CORS | `browser_hosted_cors_preflight_spec.spl`; public-only OPTIONS validates before the actual job under one terminal owner/deadline and no preflight side effects. | STATIC SECURITY REVIEW PASS; direct-host CORS/live execution RED |
| Inert iframe DrawIR | `simple_web_iframe_draw_ir_embedding_spec.spl`; child batches preserve order/clip/IDs/materials and clear child hit authority, with grouped fail-closed placeholders. | STATIC REVIEW PASS; legacy pixel parity/caller migration/child runtime authority RED |

## Reviewed browser hardening evidence reconciliation (2026-07-31)

All entries are source/spec/manual review results only; prior RED/FAIL history
and the absent admitted pure-Simple runtime receipt remain unchanged.

| Requirement area | Evidence | Status |
|---|---|---|
| DOM generation routes and rollback | `browser_dom_identity_generation_spec.spl` and its manual, integrated through `2155e6a31fc`, cover index construction, stable dispatch, handler replacement, stale rejection, rejected-eval rollback, and stale worker cleanup. | STATIC REVIEW PASS; runtime/NFR/10,000-cycle receipt HELD |
| Disabled text input | `fbecc67eb77` uses shared UI access before dispatch. | STATIC REVIEW PASS; execution HELD |
| Animation layout keys | `f57d9bc4600` and `782477146a9` cover unused layout-key suppression and an empty final keyframe. | STATIC REVIEW PASS / PERF-EVIDENCE-HELD; lifecycle/multi-list RED |
| Hosted form action | `browser_form_action_authorization_spec.spl` and its manual cover `c91fdc0e67b` host-owned conservative authorization. | STATIC REVIEW PASS; execution HELD |
| CORS unsafe headers | `browser_fetch_cors_unsafe_header_preflight_spec.spl` and its manual cover `bf7dfff029a` direct Simple broker OPTIONS admission and denied-policy suppression. | STATIC/EVIDENCE-HELD; hosted non-simple/live preflight RED |
| TLS and mixed content | Existing TLS failure and redirect mixed-content source/spec rows remain available. | SOURCE PRESENT / LIVE EVIDENCE HELD |

`be08f84be5c` + `1d16db5e149` + `dc55d6dffde` + `ca91c19d7f8` pass static
review for supported `N`/`Npx`, duplicate, `initial`, `unset`, and
default-parent-inherit gap cases only. Nonzero `inherit`, `revert-layer`, and
qualified execution remain RED.

## Qualified full-CLI evidence hold (2026-07-31)

One source-scoped full-CLI native-build was attempted with the pure-Simple
phase-2 `stage2-runtime-authority`, stub fallback disabled, two threads, and
the cache preserved. It was stopped after about 75 minutes of continuous
approximately 99.8% CPU use and stable approximately 2.4--2.5 GiB RSS. It had
emitted dependency warnings but no output artifact and zero cache files. This
records a compiler progress/performance blocker without claiming a memory
leak. No retry, Rust seed, or full bootstrap was used. Dynamic HTML, CSS,
Draw IR, Engine2D, event, animation, security, and HTTPS evidence remains
`HELD`; it is neither runtime `FAIL` nor runtime `PASS`.

## Disabled-fieldset sequential-focus evidence (2026-07-31)

`browser_disabled_fieldset_sequential_focus_spec.spl` covers
REQ-WEB-BROWSER-004/007/008/021 through the production hosted keyboard route.
It requires positive and regular controls disabled by a fieldset to be absent
from forward, reverse, and wrapped Tab order while preserving the first legend
exception and a non-form focusable descendant. Focus/blur receipts and live DOM
routes precede semantic Draw IR color assertions and software Engine2D pixels.
The mirrored manual is
`doc/06_spec/03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.md`.
Status remains **STATIC / EXECUTION HELD** until an admitted current
pure-Simple runner and docgen execute the scenario.

## REQ-WEB-BROWSER-014 — startup-failure row closed, render route wired (2026-08-16)

The plan row lists three evidence items for this requirement: *syscall denial*,
*typed broker success*, *startup failure*. Status after this change:

| item | evidence | state |
|---|---|---|
| syscall denial | `socket()` SIGSYS-killed by `SECCOMP_RET_KILL_PROCESS` under the real `rt_browser_renderer_sandbox_enter` | native PASS |
| startup failure | non-empty `envp` fatal with exit 126; `sandbox_enter` refuses without preinit | native PASS (new) |
| typed broker success | broker -> jailed worker -> Draw IR -> pixels | code complete, NOT executed |

`scripts/check/check-browser-renderer-sandbox-seccomp.shs` now reports
`PASS — 6 check(s) verified`. The count is ACCUMULATED as each self-check
passes; it was previously a hardcoded literal `4`, which would have kept
claiming four even if a check were deleted.

New self-check: `src/runtime/test/rt_browser_renderer_startup_failure_selfcheck.c`.
Neither of its arms can SKIP — both fire before any kernel capability is
consulted, so a host without seccomp or Landlock still decides them. Both were
sabotage-tested and both FAIL under sabotage.

The render route is wired (`src/app/browser/sandbox_render.spl`). The blocker
previously recorded here — "the broker returns `DrawIrComposition`, not
`[u32]`, and no rasterizer exists" — was **false**;
`Engine2dCompositorBackend.render_draw_ir_composition`
(`src/os/compositor/compositor_engine2d.spl:364`) has 20 call sites. See the
bug record for how a `.gitignore`-honouring `grep` wrapper produced that false
absence, and `.claude/skills/spipe.md` for the rule that now prevents it.

**Not promoted.** The sandboxed render has never executed: the Rust seed lacks
the `rt_browser_renderer_spawn_sandboxed` extern, and no admitted pure-Simple
runtime exists on this host. Diagnostic seed observations (not lane evidence):
the browser runs and renders real glyphs (`61 pixels painted`; GUI captured
under Xvfb at 64x36 with 15 distinct colours), and all three routing states
report distinct, correct reasons.

Out of scope and explicitly NOT claimed: rendering a real remote page. The app
returns `"(no page loaded for {url})"` for every URL except `simple://home`
(`src/app/browser/render_adapter.spl:110-113`). Real TLS/HTTP exists but is
wired only into the hosted worker browser.

## REQ-WEB-BROWSER-015 — scheme gate landed, real fetch merged (2026-08-16)

`src/app/browser/page_loader.spl` closes the enforcement gap: until now NO
code in the app validated URL schemes at all — any string was accepted. The
gate allows top-level http/https plus `simple://home`; file/data/javascript/
custom schemes are refused with a reason naming this requirement.

The same module merges the browser fronts onto ONE fetch path: the app browser
now loads real pages through `FetchEngine` — the engine already carrying the
hosted worker browser's cache/CORS surface — instead of a stub. No second
fetch implementation exists.

Evidence tiers, kept honest:
- Unit (EXECUTED, seed interpreter): `browser_page_loader_spec.spl` — 3/3
  passed, counted verdict `executed=3`. Gate logic only, no network.
- Live (seed, diagnostic): `http://example.com` fetched (559 bytes) and the
  ORIGIN'S document rendered by the engine; `file://` refused with the
  REQ-015 reason.
- UPDATE 2026-08-16: the seed TLS stubs were replaced with real delegates to
  the runtime rustls client (`interpreter_extern/net_tls_client.rs`, driver
  `runtime-tls` feature). Live under the seed: `https://example.com` loads
  (559 bytes, chunked transfer decoded) and `https://self-signed.badssl.com`
  is rejected by the certificate verifier. Seed evidence remains diagnostic
  tier — promotion still requires the self-hosted binary.

Also fixed en route: `h1_client.spl:get_mock_registry` used `.?` +
`.unwrap()`, which the seed's semantic pass cannot resolve after narrowing
("method `unwrap` not found") — every live fetch died before reaching the
network. Rewritten as an optional `match` (the dominant idiom, valid under
both runtimes).
