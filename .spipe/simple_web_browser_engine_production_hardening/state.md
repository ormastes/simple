# Feature: simple-web-browser-engine-production-hardening

## Raw Request

`$sp_dev harden simple web browser. 1. check html rendering and fix 2. check css rendering check and fix 3. simple script and javascript to animiation check and fix. 4. check security sandbox has hole and fix. 5. button, text input and other events works properly. 6. go forward, backward, stop. home, bookmark. url input etc feature exists and works. 7. check https protocol supported. make simple web browser in production level. fix bugs. which simple web engine and simple 2d engine might have or even js engine. deep research current and web then plan for pherallle agents to make it production level.`

Follow-up: `b b and there might bug gc use and other perf bug fix them too.`

## Task Type

feature

## Refined Goal

Make the Simple browser a production-ready, fail-closed web client whose
HTML/CSS rendering, Simple Script and JavaScript animation, DOM input events,
navigation chrome, HTTPS transport, sandbox boundaries, GC lifecycle, and
Simple Web/Engine2D/JS performance are proved by executable evidence.

## Acceptance Criteria

- AC-1: One documented canonical BrowserSession → Simple Web → Draw IR →
  Engine2D path renders the selected HTML/CSS profile.
- AC-2: JavaScript and Simple Script mutate the live DOM and produce
  time-evolving timer/rAF/CSS animation frames on one monotonic clock.
- AC-3: Pointer, keyboard, focus, text editing, forms, scrolling, and default
  actions use one capture/target/bubble event path.
- AC-4: Back, forward, stop, reload, home, bookmark, links, and address entry
  work in the production surface with correct history and cancellation.
- AC-5: HTTP/HTTPS, redirects, URL resolution, trust-store and service-identity
  validation work; invalid certificates fail closed.
- AC-6: Same-origin, CORS, CSP, mixed-content, cookie/storage, schemes, and
  renderer capabilities fail closed.
- AC-7: Hostile page work runs in an OS-sandboxed site renderer without Node,
  filesystem, process, environment, listener, device, or generic IPC access.
- AC-8: Parser/script/resource/IPC limits and fuzz corpora prevent crashes,
  hangs, unbounded allocations, and sandbox escape.
- AC-9: Navigation/close/crash release DOM, JS, event, timer, image, layout,
  Draw IR, and renderer resources without stale callbacks or retained cycles.
- AC-10: Selected startup/render/frame/input/RSS/GC/soak/regression budgets pass
  on production binaries.
- AC-11: Every selected requirement traces to fail-closed SSpec, manual, and
  platform evidence; unavailable rows never count PASS.
- AC-12: Architecture, detail design, system-test plan, parallel-agent plan,
  operator guide, and generated manuals match shipped behavior.

## Scope Exclusions

- No claim of complete HTML/CSS/ECMAScript/Web API parity.
- Engine3D is outside this browser/GUI/Web/Engine2D lane.
- The narrower `simple_web_browser_production_hardening` UI server/auth lane
  remains independently owned.

## Cooperative Review

- Sidecars: security, render/GC, UI/events, and SSpec/evidence.
- Merge owner and final reviewer: root normal/highest-capability Codex.
- Spark was requested but unavailable.
- Frozen names and steps are recorded in
  `doc/03_plan/agent_tasks/simple_web_browser_engine_production_hardening.md`.
- Unimplemented evidence helpers fail explicitly with `fail(...)`.

## Phase

implementation in progress / target evidence blocked

## Log

- dev: Created a separate broad browser-engine lane.
- research: Parallel code, document, standards, and security research found
  unrestricted `file://`, page-visible Node globals, cookie isolation gaps,
  broken address input, zero-time-only animation, duplicate semantic paths,
  missing live browser TLS/sandbox, and absent GC/performance proof.
- requirements: User selected Feature B and NFR B and added GC/performance bug
  fixing. Final `REQ-WEB-BROWSER-001..021` and
  `NFR-WEB-BROWSER-001..017` include lifecycle, leak/soak, GC pause, RSS, and
  regression gates.
- design: Added architecture/TLDR, GUI/TUI/detail design, system-test and
  parallel-agent plans, plus fail-closed production/security/performance SSpec
  contracts.
- implementation: Removed BrowserSession `file://` reads and page-visible Node
  globals; added address edit/submit, reload, favorite toggle, canceled-response
  rejection, document-state release, and inflight-request consumption.
- implementation: Added one monotonic JS timer clock, BrowserSession
  `advance_time`, and `requestAnimationFrame`/`cancelAnimationFrame`.
- implementation: Added one DOM event route with normalized listener names,
  capture/target/bubble ordering, cancellation and propagation state, pointer
  payloads, keyboard activation, interactive-element default actions, and
  ScriptHost application to the addressed target node.
- implementation: Hardened the shared HTTP/HTTPS path: raw request headers now
  serialize consistently in HTTP/1 and HTTP/2, URL/origin methods exist,
  unsupported schemes fail closed, TLS rejects disabled peer verification,
  unknown protocols, and minimum-version downgrades, CORS binds exact origins
  and requested methods, credentialed wildcard origins are denied, same-origin
  cookies cannot leak cross-origin, credentialed responses do not enter the
  URL-only cache, and scripts cannot inject transport-owned headers.
- implementation: Closed the live BrowserSession host-pump bypass: non-network
  requests are discarded at the export boundary and cross-origin page fetches
  are rejected before host network access until request mode and validated CORS
  response metadata are carried end to end.
- implementation: Closed the page-visible transport-cookie capability leak.
  Browser runtime creation now exposes only non-HttpOnly `document.cookie`;
  request cookies remain in BrowserSession, which strips caller `Cookie` lines
  and attaches the scoped jar value. Internal fetch/module state is no longer
  installed on `window`, `chrome`, or globals.
- implementation: Deleted the unused synchronous JS fetch helper and its raw
  file/HTTP imports. Browser-profile `fetch()` only queues a request for the
  BrowserSession policy boundary.
- implementation: Corrected capture/bubble listener mutation to apply to each
  listener's `currentTarget`, not always the event target.
- implementation: Radio selection now clears only named peers owned by the
  same form. The shared root-aware default-action helper is reused by
  ScriptHost and BrowserSession, while same-named radios in other forms remain
  selected.
- implementation: Home navigation now uses the normal BrowserSession network
  navigation path, so an unregistered HTTP/HTTPS home page queues a document
  request instead of returning the old "network navigation is not implemented"
  error.
- implementation: Replaced BrowserSession's fake text-node DOM count/layout
  pass with the real HTML tree builder and direct node counting.
- implementation: BrowserSession now owns the parsed body DOM, gives every
  node a stable identity, serializes DOM mutations back into the live script
  host, and routes UI-access links, buttons, checkboxes, and text input through
  that same event path.
- implementation: Back/forward navigation now clears the prior page runtime,
  timers, requests, and DOM before loading the history entry.
- implementation: Raw `<style>`/`<noscript>` text no longer leaks into visible
  body DOM during tree construction.
- implementation: Simple Script `body_text`/`body_html` writes now rebuild the
  owned DOM, so subsequent rendering, node counts, and UI events observe the
  same page state.
- optimization: Closed two per-frame Engine2D lifetime leaks by shutting down
  requested GPU backends after readback in both GPU-paint and upload paths.
- optimization: Removed FetchEngine's duplicate DNS resolution; H1 now owns
  the single lookup for each request and preflight.
- implementation: H1 mock responses are resolved before DNS/TCP/TLS, so
  deterministic HTTPS tests cannot accidentally reach the network.
- implementation: Fetch now rejects HTTPS-to-plaintext redirects before
  constructing or dispatching the redirected request.
- optimization: H1 no longer performs a DNS lookup for HTTPS and discards the
  address before the TLS runtime resolves/connects the authenticated hostname.
  Plain HTTP retains its single H1-owned lookup.
- implementation: Removed the false H1 connection pool. Both response readers
  consume to EOF and close the transport, so retained pool entries were stale
  copies that could reuse closed descriptors and eventually lock out a host.
  H1 uses honest one-shot connections until framed keep-alive exists.
- evidence: Added a real HTML/CSS/Simple Script/JavaScript two-frame Engine2D
  integration spec and standalone native fixture. The fixture has Simple
  Script create the CSS-targeted red first frame, then JavaScript rAF creates
  the blue second frame. Interpreter execution timed
  out at 180 seconds; native entry-closure build timed out at 240 seconds after
  parser blockers were normalized. Details:
  `doc/08_tracking/bug/browser_session_animation_target_build_blockers_2026-07-26.md`.
- evidence: The deployed `bin/release/x86_64-unknown-linux-gnu/simple` is
  byte-for-byte identical to the Rust bootstrap seed, so it cannot provide
  production evidence. A bounded run with an existing pure-Simple stage-2
  binary also failed before fixture `main` because the documented
  `--mode=interpreter` value was rejected as an unknown argument. No render
  PASS is claimed.
- evidence: A direct `build/native_probe/simple run` of the animation fixture
  confirmed that the probe is also a Rust bootstrap seed; it emitted over 8 MB
  of misleading diagnostics and rejected its internally selected interpreter
  mode before fixture `main`. No bootstrap or compiler edit was attempted.
- evidence: The genuine staged stage-3 pure-Simple artifact is a bootstrap
  native-build compiler only and exposes no `run`/`test`/`check` command, so it
  cannot execute the fixture directly.
- evidence: A narrow Cranelift `native-build` with that genuine stage-3
  compiler completed three bounded fix/rebuild cycles. Two BrowserSession
  enum-variant `if val` sites were normalized to `match`; the third cycle then
  confirmed the same parser defect in three shared async-JS-interpreter sites.
  The hard cycle cap was reached, so no fourth workaround, compiler edit, or
  bootstrap was attempted and no render PASS is claimed.
- compiler: Confirmed and fixed the shared parser root cause: qualified enum
  constructors are `EXPR_METHOD_CALL`, which `if val` failed to admit/desugar.
  Existing qualified-enum coverage already exercises the grammar.
- evidence: Three bounded compiler-production attempts accepted the parser
  change through object generation but produced no executable: one encountered
  another session's `runtime.h` conflict markers, one clean-worktree link
  lacked the compiler/Cranelift runtime ABI, and one genuine-full-CLI build
  stayed silent for three minutes and was terminated. No fourth build was run.
- evidence: A direct source-run probe with the existing full CLI still
  delegated to the Rust seed and stopped before fixture `main` on an unlocated
  BrowserSession runtime parse error. Correcting one malformed closing-call
  indentation did not change that result on the single bounded rerun; no real
  frame PASS is claimed.
- evidence: Scoped diff validation passes for the radio/home fixes and focused
  specs. The currently deployed release binary has changed hash since the
  earlier probe but still prints the Rust-bootstrap-seed warning, so the new
  specs were not run through it and no production PASS is claimed.
- evidence: Added a focused security regression proving HttpOnly cookies are
  absent from page JS, internal module state is undefined, a forged internal
  cookie property is ignored, and the sanitized same-origin request still
  receives the real transport cookie jar. Working and staged direct-runtime
  access guards pass; executable spec evidence remains pending a genuine
  pure-Simple CLI.
- evidence: Added an offline HTTPS downgrade regression with both redirect
  endpoints registered; the request must fail before the plaintext mock can be
  consumed. Source and documentation now distinguish rustls-enabled runtime
  TLS from the fail-closed stub. Live HTTPS remains unproven until a genuine
  pure-Simple binary is linked with runtime TLS.
- evidence: Focused diff validation and both required
  `direct-env-runtime-guard` working/staged audits passed after the current
  browser/session/render changes.
- evidence: Added DOM-backed input/event integration and UI-access system
  specs. The language service parsed the changed tree builder, UI-access
  adapter, and script/CSS animation spec; this is syntax evidence only because
  no genuine production runtime can currently execute the fixture.
- evidence: Three bounded pure-Simple checks of the hardened CORS module
  corrected compact-expression and instance-method syntax, then stopped on the
  remaining `if not is_simple_method(...)` parser failure. No fourth retry was
  run. Details:
  `doc/08_tracking/bug/browser_network_policy_check_blocker_2026-07-26.md`.
- implementation: Clicking a submit-capable `<button>` or
  `<input type="submit">` now resolves its actual owning form (including an
  explicit `form=` owner), dispatches a cancelable bubbling `submit` event,
  and applies the form default only when that event is not prevented.
  `type=button` and controls without a form do not synthesize submission.
- evidence: Added focused Simple-host same-form/prevent-default coverage and a
  BrowserSession inline `onsubmit` integration regression. Scoped
  `git diff --check` passes. Source-mode LSP diagnostics reported their known
  `simple check` subprocess deadlock, so executable PASS is not claimed and no
  bootstrap/retry was attempted.
- implementation: Stop now covers the complete BrowserSession load lifecycle,
  not only the initial document request. The toolbar remains enabled while
  stylesheet, script, module, wasm, or fetch work is queued/inflight; stopping
  preserves the visible partial document, completed CSS, and history entry,
  releases pending/inflight/load state, and causes late responses to fail as
  canceled.
- evidence: Added focused lifecycle and textual UI-access regressions for a
  committed document blocked on an external stylesheet. Scoped
  `git diff --check` passes; executable PASS remains pending the genuine
  pure-Simple CLI and no bootstrap was attempted.
- implementation: Network/address navigation now uses one fail-closed
  normalization boundary. It trims input, canonicalizes mixed-case HTTP(S),
  upgrades bare hosts to HTTPS, preserves `about:blank`, and rejects
  file/javascript/data/blob/FTP/WebSocket or other explicit unsupported
  `://` schemes before the search fallback can rewrite them.
- refactor: Removed a tracked byte-identical duplicate of the RFC 3986
  dot-segment helpers from `browser_session_url.spl`; the file now has one
  definition per URL helper.
- evidence: Added bare-host HTTPS and explicit unsafe-scheme regressions.
  Duplicate-symbol scan and scoped `git diff --check` pass; executable PASS is
  still not claimed and no bootstrap was attempted.
- security/performance: Bounded the active browser JavaScript timer drain to
  1,000 due tasks per call. A far-future clock advance can no longer spend
  unbounded CPU replaying a short interval, and a non-callable repeating timer
  can no longer spin forever merely because executed-callback count stays zero.
  Remaining overdue work yields for a later drain.
- evidence: Added a focused billion-millisecond interval regression that must
  return after exactly 1,000 callbacks. The canonical lib/std hardlink is
  consistent and scoped `git diff --check` passes; executable PASS remains
  blocked by the known target CLI issue and no bootstrap was attempted.
- GC/security/performance: Capped retained timer handles and queued timer or
  `nextTick` tasks at 4,096 per page runtime. This bounds the interpreter's
  strong handle arrays without breaking observable completed-handle
  `refresh()`/`clearTimeout()` semantics; excess scheduling returns undefined
  and emits a bounded diagnostic.
- evidence: Extended the timer-limit regression to verify exactly four of
  4,100 scheduled handles are denied. Canonical lib/std hardlink and scoped
  `git diff --check` pass; executable PASS remains pending.
- security/performance: Added a 50 MiB HTTP/1 response accumulation ceiling,
  reusing the canonical cache entry limit. Plain TCP and TLS readers reject
  before appending the over-limit chunk, close their transport on error, and
  mock responses are rejected before body conversion. This bounds raw
  HTML/CSS/script/Wasm input before BrowserSession parsing.
- evidence: Added exact-boundary response-size arithmetic coverage; scoped
  `git diff --check` passes. HTTP/2/decompression limits remain separate
  unfinished AC-8 work, and executable PASS is not claimed.
- research/performance: Confirmed CSS keyframe animation is not wired into the
  production renderer. Production style processing parsed a
  `KeyframeRegistry` and discarded it; `AnimationEngine` and
  `AnimationController` have no production callers, and
  `BrowserSession.advance_time()` advances JavaScript only. Removed the
  discarded hostile-input parse.
- blocker: The existing two-frame fixture proves Simple Script DOM creation,
  static CSS application, JavaScript rAF mutation, and Engine2D repaint; it
  does not prove CSS `@keyframes`. The required canonical clock/style/Draw IR
  integration and pixel evidence are documented in
  `doc/08_tracking/bug/browser_css_animation_clock_not_connected_2026-07-26.md`.
- security/rendering: Escaped page-controlled `document.title` text at the
  canonical BrowserSession render-document serializer. A title can no longer
  close `<title>` and inject style/body markup into the next parsed frame.
- evidence: Added an exact `</title><style>` injection regression; scoped
  `git diff --check` passes and executable PASS remains pending.
- implementation: Completed the missing bookmark-open half of browser chrome.
  Saved favorites now appear as stable actionable bookmark links in the
  BrowserSession UI-access snapshot and open through the normal fail-closed
  network navigation boundary. The existing Favorite control remains the
  add/remove toggle.
- evidence: Added a textual production-surface add/list/open bookmark scenario
  using a registered HTTPS page. Scoped `git diff --check` passes; executable
  and generated-manual evidence remain pending.
- blocker: Bookmark persistence across browser restarts is not implemented.
  No browser/profile settings owner exists above BrowserSession, and adding
  direct profile-file access to the session would violate the sandbox
  boundary. The required typed broker, bounds, atomic storage, and restart
  evidence are documented in
  `doc/08_tracking/bug/browser_bookmark_persistence_owner_missing_2026-07-26.md`.
- security: Fixed URL authority parsing at the shared BrowserSession boundary.
  Origins now exclude query/fragment and credentials, cookies scope by hostname
  rather than port, and network navigation rejects empty, credential-bearing,
  whitespace, and backslash authorities.
- evidence: Added focused URL authority and cross-port cookie regressions.
  Scoped `git diff --check` and duplicate-helper validation pass. Executable
  rendering evidence remains blocked by the already-recorded target CLI
  compiler failure; no bootstrap or retry was attempted.
- security/performance: Hardened the live HTTP/1 response decoder at its shared
  framing boundary. Duplicate, invalid, or oversized Content-Length values,
  Transfer-Encoding conflicts, unsupported transfer codings, truncated bodies,
  malformed chunks, missing terminators, and decoded bodies above 50 MiB now
  fail closed instead of returning partial or ambiguously framed content.
- evidence: Added focused exact-limit, ambiguity, truncation, valid chunk
  extension, and malformed terminal-chunk regressions. HTTP/2 response transport
  remains fail-closed and the browser has no content-decompression path, so no
  dead limit scaffolding was added there. Scoped static checks pass; executable
  PASS remains blocked and is not claimed.
- security: Hardened the shared address/navigation authority boundary against
  invalid DNS labels, nonnumeric/zero/out-of-range ports, multiple colons, and
  bracketed IPv6. IPv6 is intentionally fail-closed because the current
  transport URL parser splits it at the first colon and would misroute it.
- evidence: Added focused valid host/port and malformed authority regressions.
  Canonical lib/std hardlink, duplicate-helper scan, and scoped
  `git diff --check` pass; no runtime or bootstrap retry was made.
- HTTPS/correctness: Added one canonical `Url.authority()` formatter and reused
  it for URL text, HTTP/1 Host, and HTTP/2 `:authority`. Non-default HTTPS ports
  now reach the same virtual origin selected by the TLS socket instead of being
  silently omitted from request routing.
- evidence: Added HTTP/1 and HTTP/2 `https://example.test:8443` authority
  regressions. Canonical lib/std hardlinks and scoped static checks pass;
  executable TLS evidence remains blocked and is not claimed.
- correctness: HTTP/1 plain and TLS request sends now require the runtime to
  report the complete byte count. Positive short writes close the transport and
  fail instead of sending a truncated request and reading a misleading response.
- evidence: Added exact/short/error write-count coverage; scoped static checks
  pass and executable network evidence remains pending.
- security: Made Host, Connection, Content-Length, Transfer-Encoding, and TE
  transport-owned at the shared FetchRequest boundary. HTTP/1 now discards
  caller framing and regenerates one canonical Host/close/body-length set;
  HTTP/2 omits connection-specific and caller framing fields.
- evidence: Added a request-smuggling regression with forged authority, length,
  chunking, and keep-alive headers while preserving an ordinary application
  header. Canonical lib/std hardlinks and scoped static checks pass.
- security/performance: Promoted the 50 MiB resource ceiling to the shared
  request boundary. BrowserSession now rejects oversized host-pump responses
  before HTML/CSS/JS/module/Wasm processing and rejects oversized direct HTML
  before tree construction; failed document/resource loads are stopped and
  oversized fetch promises receive an error.
- evidence: Added exact-boundary arithmetic coverage and verified all H1,
  BrowserSession response, and direct document paths reuse the shared limit.
  Scoped static checks and canonical lib/std hardlinks pass.
- implementation/security: Unified control focus ownership in the DOM default
  action path. Text editing dispatches focus before input; activating buttons,
  checkboxes, radios, or submit controls moves the single document focus
  marker. UI access now reports that state, exposes textarea editing, omits
  hidden inputs, masks password values, and does not advertise readonly fields
  as editable.
- evidence: Added focused-event/single-owner DOM coverage plus production
  UI-access hidden/password/textarea/focus scenarios. Replaced a non-built-in
  negative matcher in the touched spec. Canonical lib/std hardlinks and scoped
  static checks pass; executable evidence remains pending.
- implementation/security: Connected uncanceled form submit defaults to the
  BrowserSession navigation pump. The canonical live DOM now serializes UTF-8
  successful input/textarea/select controls and the activated submitter,
  honors action/method/enctype submitter overrides, queues GET or urlencoded
  POST document requests, and fails closed on unsupported POST encodings.
  `preventDefault()` still blocks submission.
- refactor/evidence: The legacy browser shell now reuses the same UTF-8 form
  encoder instead of its incorrect code-point encoder. Added Unicode,
  checkbox/select/textarea/submitter, unsupported-enctype, live-value POST, and
  canceled-submit regressions. New lib/std module is hardlinked and scoped
  static checks pass; executable evidence remains pending.
- implementation/security: Address-bar search text now uses the same byte-safe
  UTF-8 query encoder as form submission. Spaces, delimiters, and non-ASCII text
  stay inside one `q` value instead of creating invalid URLs or injected query
  parameters.
- evidence: Added exact `Ada & 한` encoder and normalized search URL
  regressions. Removed the duplicate encoder body; canonical lib/std hardlinks,
  duplicate-helper scan, and scoped static checks pass.
- security: Replaced prefix-based loopback trust with one exact parsed-host
  helper shared by secure-context exposure and both mixed-content request
  producers. `localhost.evil` and `127.0.0.1.evil` can no longer inherit
  loopback security exceptions.
- evidence: Added exact loopback/port and spoofed-host helper coverage plus a
  live HTTPS-page fetch rejection scenario. No stale prefix checks remain;
  canonical lib/std hardlinks and scoped static checks pass.
- correctness/security: Canonicalized explicit HTTP `:80` and HTTPS `:443`
  spellings in the shared BrowserSession origin helper. Same-origin fetch and
  runtime `location.origin` no longer disagree merely because a default port
  was written explicitly; non-default ports remain origin-significant.
- evidence: Added default, zero-padded default, and non-default port origin
  regressions. Scoped static and duplicate-helper checks pass.
- correctness/security: Document and fetch redirects now share validated
  network targets, a 20-hop ceiling, HTTP redirect method/body rules, and HTTPS
  downgrade rejection. Fetch redirects remain same-origin until CORS metadata
  exists; 307/308 preserve request content type while rewritten GET requests
  clear it. Redirect bodies are not committed as documents.
- evidence: Added focused document 303 and downgrade regressions and tightened
  existing fetch 303/307 checks. Canonical lib/std hardlink and scoped
  `git diff --check` pass. The real Simple/JS/CSS animation fixture still cannot
  execute because of the recorded pure-Simple target compiler blocker; no
  runtime PASS or bootstrap claim is made.
- implementation/security: Added a typed bookmark snapshot boundary without
  giving BrowserSession profile-file access. Snapshot load revalidates schemes
  through the canonical navigation policy, bounds URL/title sizes and entry
  count, and copies arrays so hostile or stale profile data cannot alias live
  session state. Direct bookmark adds use the same validation.
- evidence: Added snapshot isolation and malformed `javascript:`/`file:`
  rejection coverage. Scoped static checks and the canonical lib/std hardlink
  pass. Cross-process atomic persistence is still correctly tracked as missing
  because no production browser-profile owner is wired to BrowserSession.
- security: Home-page configuration now uses the same bounded network URL
  policy as direct navigation. Invalid `file:`, executable, unknown, and
  oversized values are rejected without replacing the last safe home page;
  `try_set_home_url` exposes the result to chrome/settings owners.
- security/correctness: Centralized active-subresource enforcement in the
  request pump. HTTPS documents now block non-loopback HTTP CSS, classic
  scripts, modules, and Wasm; modules/Wasm also fail closed cross-origin until
  response CORS metadata is modeled. Non-network active resources are rejected.
  Each rejection is committed as a synthetic load error so stylesheet/script
  sequencing advances instead of hanging the document.
- evidence: Added one live HTTPS document scenario covering mixed CSS/script
  and cross-origin module rejection plus loader convergence. Scoped static
  checks and the canonical lib/std hardlink pass; executable evidence remains
  blocked and is not claimed.
- correctness/security: External CSS, classic scripts, and same-origin Wasm
  now follow bounded validated redirects, retain response-cookie processing,
  and reject HTTPS downgrade. All executable/style resources reject non-2xx
  HTTP bodies instead of parsing or executing server error pages.
- evidence: Added stylesheet redirect request evidence and a 404 JavaScript
  body non-execution regression.
- correctness: Module requests now retain their original URL across redirects
  and the loader records original-to-final identity. Root modules resume from
  the fetched source instead of the previous empty placeholder, redirected
  modules resolve relative imports against the final response URL, and cached
  original specifiers map to the already evaluated final module.
- evidence: Added a same-origin module redirect whose final source imports a
  relative dependency; the expected dependency request is rooted at the final
  URL and completion updates the document title. Scoped static checks pass.
- security/performance: Added a shared 1024-entry per-document subresource
  ceiling. Script tags, stylesheet tags/links, nested CSS imports, and module
  dependency extraction stop at the bound; stylesheet insertion cannot grow
  past it. The active load records visible warnings when a parser reaches the
  ceiling, limiting hostile-page request fan-out, retained source arrays, and
  interpreter work.
- evidence: Added exact 1024/1025 boundary coverage and a 1025-script document
  regression. Canonical lib/std hardlinks and scoped static checks pass.
- security/performance: Extended resource bounding to runtime work. The JS
  engine rejects `fetch()` with an already-rejected promise once 1024 requests
  are outstanding, and BrowserSession enforces a 1024 total subresource
  dispatch budget per navigation across fetches, redirects, CSS, scripts,
  modules, and Wasm. Navigation resets the budget. Overflowed loader requests
  receive synthetic errors so sequencing still converges.
- evidence: Added a live JavaScript fetch rejection at the exhausted document
  budget. JS/browser canonical hardlinks and scoped static checks pass.
- implementation: Repaired the existing CSS `AnimationEngine` target contract.
  `Animation` now carries a DOM `node_id`, `create_for_node` constructs targeted
  instances, and every interpolated `StyleUpdate` preserves that identity
  instead of incorrectly targeting node zero. `Transition` now uses the same
  compatible target-aware constructor and update path.
- evidence: Added focused midpoint animation and transition regressions for
  nodes 42 and 77.
  Static checks and canonical lib/std hardlinks pass. This removes one engine
  blocker but does not yet connect keyframes to the production renderer clock.
- security/performance: Bounded the dormant animation engine before wiring it:
  at most 1024 animations, 1024 transitions, and 4096 emitted style updates per
  tick. Full update buffers stop further interpolation work for the frame.
- evidence: Added exact active-capacity boundary coverage; scoped static checks
  pass.
- design finding: CSS animation cannot be honestly fixed by merely ticking the
  existing `AnimationEngine`: the canonical HTML/CSS renderer still receives
  no frame time and retains no per-document keyframe registry. A
  BrowserSession-only override stylesheet would create a second cascade, so
  that shortcut was not added; the production-blocker record remains
  authoritative.
- correctness/evidence: `@keyframes` declarations now enter interpolation as
  typed colors, pixel lengths, percentages, and numeric values instead of
  opaque keywords; color interpolation also preserves alpha. A focused
  parser-to-midpoint regression covers red-to-blue color, 10-to-20px width,
  and 0-to-1 opacity on node 42. Scoped static checks and canonical lib/std
  hardlinks pass; the renderer clock and executable evidence remain blocked.
- security/performance: BrowserSession cookie parsing now rejects CR/LF before
  storage, closing the page/response-to-outbound-header injection path.
  Individual cookies are capped at 4096 bytes, per-domain retention at 50, and
  the session jar at 3000, bounding retained heap and generated Cookie headers.
- evidence: Added focused injection, oversize, and 51st-cookie regressions and
  refreshed the mirrored cookie manual. Canonical lib/std hardlinks and scoped
  static checks pass; executable evidence remains blocked by the recorded
  target compiler issue. Public-suffix validation remains separately tracked.
- security: Added a document-scoped CSP source-list gate before active content
  enters the loader or JS request pump. `default-src` fallback and explicit
  `style-src`, `script-src`, and `connect-src` now enforce `'none'`, `'self'`,
  `'unsafe-inline'`, wildcard, scheme, and exact-origin sources for inline and
  external CSS, JavaScript, Simple Script, modules, Wasm, and fetch.
- correctness/evidence: CSP is captured only from the successful document
  response, retained in history/reload entries, reset on navigation, and never
  overwritten by redirect or subresource headers. Added a focused network
  document scenario proving allowed inline JS plus pre-dispatch denial of
  inline/external CSS, external JS, and same-origin fetch. Mirrored manual,
  first-directive precedence, multi-header policy intersection, canonical
  hardlinks, and scoped static checks pass; executable evidence remains
  compiler-blocked.
- HTTPS/security: BrowserSession now processes HSTS only from HTTPS responses,
  retains a bounded 1024-host policy set, supports `max-age` and
  `includeSubDomains`, upgrades document/subresource/fetch and redirect targets
  before downgrade policy, and expires policies on the shared deterministic
  monotonic clock.
- evidence: Added a focused HTTPS response scenario proving subdomain upgrade
  and exact max-age expiry. Canonical lib/std hardlinks and scoped static checks
  pass; live TLS execution and cross-process HSTS persistence remain unproven.
- controls/events: DOM-backed text editing now dispatches focus then cancelable
  `beforeinput` before mutation. Cancellation preserves the prior input value
  and suppresses `input`; successful edits mark the control dirty, emit
  non-cancelable `input`, and expose a UI-access `blur` action that emits
  `change` only for dirty controls before clearing focus and dispatching blur.
- evidence: Extended the production UI-access system scenario with successful
  input, change-on-blur, canceled-beforeinput, button, and checkbox behavior.
  The textual action result distinguishes canceled edits, and the mirrored
  manual now reflects all ten scenarios and current toolbar actions. Canonical
  hardlinks and scoped static checks pass; executable evidence remains blocked.
- controls/events: Focus is now a single browser-owned DOM state with event
  delivery, not only an attribute cleanup. Before any focus-producing default
  action, BrowserSession finds the prior focused node, commits a dirty text
  control through `change`, dispatches `blur`, then lets the canonical DOM
  default action clear/set focus. Explicit blur does not emit duplicate change.
- evidence: The UI-access system scenario now proves implicit dirty
  change-on-focus-transfer, exactly one focused node, and zero focused nodes
  after explicit blur. Canonical DOM/runtime lib/std hardlinks and scoped
  static checks pass; executable evidence remains blocked.
- controls/correctness: Fixed radio default-action state loss in the canonical
  DOM owner. Same-form group cleanup now transforms the already focus-cleared
  and newly focused tree instead of rebuilding from the stale pre-focus root.
- evidence: Extended the shared ScriptHost radio regression and the production
  UI-access control scenario to prove peer deselection, selected-state
  exclusivity, and focus retention on the selected radio. Scoped static checks
  and the canonical DOM lib/std hardlink pass; executable evidence remains
  blocked.
- controls/events: Connected the existing canonical keyboard activation mapper
  to BrowserSession and UI access with one `key` action for links, buttons,
  checkboxes, radios, and submit inputs. It dispatches cancelable bubbling
  `keydown`, re-reads the live target after handler mutation, then reuses the
  normal click/default-action route; prevention suppresses activation.
- evidence: The production control scenario now proves Enter button activation,
  visible keydown mutation, canceled keydown suppression, and Space radio
  selection/focus. Mirrored manual, canonical lib/std hardlinks, and scoped
  static checks pass; executable evidence remains blocked.
- security: Network URL normalization now rejects all ASCII control characters
  before navigation, closing CR/LF request-line/header injection through an
  otherwise valid authority. The central BrowserSession request pump repeats
  the same validation for internally produced CSS, script, module, Wasm, and
  fetch requests and emits a redacted `invalid-url` failure.
- evidence: Added direct URL CR/LF/tab boundaries plus a hostile script request
  injected at the pump. Both top-level and subresource routes fail before
  network export, and diagnostics do not echo the hostile URL. Mirrored URL and
  security manuals, canonical lib/std hardlinks, and scoped static checks pass;
  executable evidence remains blocked.
- JS/GC/performance: Bounded each document runtime to 4096 retained timer
  handles and each clock drain to 1000 callbacks. Non-function/over-limit
  schedules return `undefined`. Overdue intervals coalesce to one callback per
  clock advance instead of replaying every missed interval.
- correctness/evidence: Timer draining now removes/reschedules the due task
  before invoking page code, preserving nested scheduling and allowing an
  interval to cancel its own queued continuation. Added exact retention,
  nested-drain, overdue-interval, and self-cancel regressions plus a mirrored
  manual. Canonical JS lib/std hardlinks and scoped static checks pass;
  executable evidence remains blocked.
- JS/GC/performance: Promise microtask draining now yields after 1000 callbacks
  without discarding queued work, bounds retained pending handlers at 4096,
  rejects excess child promises deterministically, and removes completed
  handler/registration records so subsequent drains do not repeatedly scan
  dead closures.
- evidence: Added focused Promise queue preservation and retention-cap
  scenarios with a mirrored manual. The bounds, deferred settled reactions,
  record/property cleanup, and runtime drain surface are now on the canonical
  `nogc_sync_mut` engine used by BrowserSession; executable evidence remains
  blocked by the recorded target compiler failure.
- rendering/animation: Connected computed CSS `animation-*` properties and
  parsed `@keyframes` to BrowserSession's per-document monotonic clock. Sampled
  style updates are applied before canonical Draw IR lowering and Engine2D
  execution; navigation resets the animation epoch and keyframe sets remain
  capped at 1024.
- evidence: Extended the real Simple Script/JavaScript/CSS target fixture and
  integration spec with CSS-only start/mid/end pixel frames, plus a mirrored
  manual. Scoped diff and canonical lib/std hardlink checks pass; target
  execution remains blocked by the recorded compiler failure, so no runtime
  PASS is claimed.
- security/storage: Partitioned both `localStorage` and `sessionStorage` by
  canonical URL origin in BrowserSession. Navigation persists the departing
  origin bucket and activates only the destination origin bucket, preventing
  cross-origin reads, clears, and overwrites while preserving same-origin
  state.
- evidence: Added a bank/evil-origin isolation and restoration regression to
  the storage spec and refreshed its manual. Scoped diff and canonical lib/std
  hardlink checks pass; executable evidence remains blocked.
- JS/animation availability: Removed the canonical runtime's historical
  4096-handle lifetime gate; only concurrent pending timer work is bounded.
  This keeps a one-at-a-time `requestAnimationFrame` chain alive beyond 4096
  frames while retaining the existing pending-task resource cap.
- navigation/Stop: Document navigation is now atomic. `begin_navigation`
  cancels request-owned work but retains the committed DOM, styles, runtime,
  module/Wasm state, and CSP until a validated replacement reaches
  `_load_page_source`; Stop, response failure, and oversized responses preserve
  the active page. CSP is staged separately and commits with the document.
- controls/events: Checkbox/radio click pre-activation now occurs before click
  handlers, canceled clicks restore prior checked/radio-group state, and
  successful activation dispatches bubbling `input` then `change`. The
  standalone ScriptHost path emits the same post-activation events.
- evidence: Added stopped-document runtime/state preservation, checkbox event
  order/visible checked state, and canceled rollback regressions with refreshed
  or new manuals. CSS iteration boundaries now start the next iteration at 0%
  and new multiline conditions follow the Simple grammar rule.
- JS/security/performance: The canonical browser runtime now rejects unresolved
  `fetch()` calls above 1024 before allocating host request records while
  returning a rejected Promise. BrowserSession limits a recursive microtask
  checkpoint to eight 1000-callback batches, preventing its outer flush loop
  from multiplying the interpreter bound into one million callbacks.
- verification: The combined scoped diff check and canonical browser/JS
  lib-to-std hardlink checks pass. Runtime checks remain intentionally unrun
  because the recorded target compiler blocker exhausted its three fix cycles.
- CSS animation correctness: Preserved case-sensitive `<custom-ident>` names
  across shorthand/longhand computed styles and keyframe lookup. External
  stylesheet completion now establishes the animation epoch when styles become
  active, preventing a slow stylesheet from first painting mid-animation.
- security/storage: The canonical object owner now enforces 1024 entries and
  5 MiB of key/value text per Web Storage area for both `setItem` and direct
  property assignment, while allowing replacement of existing keys at the
  entry limit.
- evidence: Added case-sensitive/external-style animation frames and storage
  method/property quota regressions. Their scoped diff and canonical lib/std
  hardlink checks pass; executable evidence remains compiler-blocked.
- CSS animation security/performance: Keyframes are insertion-sorted once
  during stylesheet parsing and each rule is capped at 256 frames, avoiding
  repeated render-time normalization and hostile unbounded frame retention.
- cookie security: The shared URL cookie parser now enforces `__Secure-` and
  `__Host-` invariants, requires Secure for `SameSite=None`, and rejects
  unsupported `Partitioned` cookies instead of leaking them cross-partition.
- cookie public-suffix security: Added a generated pure-Simple binary-search
  owner pinned to official PSL commit
  `e1b8015c3b2f0f4f8c18659c2480fc1a22c07b20`, including ICANN/private,
  wildcard/exception, Unicode, and RFC 3492 ASCII rules. Domain cookies now
  reject public suffixes and IP hosts while valid registrable parents remain
  accepted. Provenance, source hash, MPL-2.0 license, and update script are
  checked in.
- evidence: The PSL generator shell syntax, scoped diff whitespace, generated
  10,698-rule count, pinned Git commit, source SHA-256, and representative
  exact/private/IDNA entries pass static validation. Cookie and PSL executable
  specs remain target-compiler-blocked; no runtime PASS is claimed.
- rendering/evidence: Added exact pixel evidence for the already-implemented
  `vh` vertical-margin sentinel: `40vh` begins at y=80 in a 200px viewport.
- JS timer correctness: Both BrowserRuntimeState creation paths now seed the
  interpreter timer clock from BrowserSession's existing monotonic clock, so
  timers created after navigation retain their relative deadline.
- CSS animation correctness: Repaired the missing at-time layout/Draw IR and
  fast Engine2D function chain. Computed animation styles now sample the exact
  case-sensitive keyframe registry with delay, iterations, direction, fill,
  pause, and timing before layout. Stylesheets retain at most 1024 keyframe
  rules and 256 frames per rule.
- production-host animation: The hosted compositor now owns CSS-only animation
  invalidation without depending on semantic input sessions. It computes a
  bounded timeline once per content revision, uses a content-local epoch,
  bypasses the static pixel cache only for animated frames, requests visible
  window frames at 16ms cadence, paints the exact finite endpoint, and then
  becomes quiescent. Infinite animations remain bounded by visible-window
  dirty scheduling; minimized windows do not request frames.
- persistence finding: No browser-profile owner exists above the sole
  production BrowserSession registry. Bookmark/HSTS restart persistence needs
  a typed profile broker; HSTS cannot persist its session-monotonic expiry
  directly.
- HSTS persistence boundary: BrowserSession now exports wall-clock snapshot
  entries and restores at most 1024 unique, unexpired, non-IP,
  non-public-suffix policies back onto its monotonic clock. Focused restart
  validation is present; the profile storage owner remains open.
- production-host script animation: Displayed hosted Web windows now create
  their BrowserSession before input, use a content-local host monotonic epoch,
  advance Simple Script/JavaScript timers every host loop, and republish DOM
  mutations through the existing Simple Web/Engine2D compositor path. The
  focused integration scenario requires CSS red, rAF blue, and distinct pixel
  frames at 0/16 ms.
- evidence: Scoped diff whitespace validation passes for the HSTS and hosted
  animation changes. Executable production evidence was not rerun because the
  recorded target compiler/link lane already exhausted its three bounded
  cycles; no bootstrap was attempted and no runtime PASS is claimed.
- profile persistence: Added a versioned, parameterized SQLite owner above
  BrowserSession for at most 256 ordered bookmarks and 1024 wall-clock HSTS
  policies. The hosted entry captures its trusted seeded browser window ID
  before runtime input, attaches the profile only to that ID, persists before
  browser-window destruction and WM shutdown, and rejects close when saving
  would lose profile state.
- evidence: Added a file-backed close/reopen/corrupt/removal integration
  scenario covering bookmark restoration, HSTS subdomain upgrade, corrupt-row
  rejection, expiry, and durable removal. Scoped whitespace, conflict-marker,
  manual-layout, and direct-runtime-access checks pass; target-process
  execution remains compiler-blocked and no runtime PASS is claimed.
- rendering/animation repair: Removed four accidentally committed jj conflict
  blocks from the canonical at-time HTML/Draw IR and Engine2D files, retaining
  both material provenance and CSS animation sampling. Restored the missing
  animation-aware pixel-cache owner used by hosted repaint scheduling.
- evidence: The existing compositor regression asserts red start pixels,
  a distinct midpoint, blue endpoint pixels, 16ms scheduling, and finite
  quiescence. Source-wide Simple conflict-marker and exact owner/caller scans
  pass; executable evidence remains compiler-blocked and was not rerun.
- security audit: Current-main review keeps the missing site-renderer process
  sandbox as critical and found additional open trust-boundary defects:
  unenforced compositor window ownership, cross-origin location/storage
  planting, CSP checks skipped after active-resource redirects, incomplete
  SameSite/HttpOnly overwrite isolation, and unauthenticated response delivery.
  These remain active AC-6..AC-8 work; no false PASS is recorded.
- security: Enforced compositor window ownership at the shared lifecycle and
  SimpleOS action-applier boundaries. Remote destroy, update, focus, geometry,
  title, minimize, maximize, and restore requests now require `src_port` to
  match the stored owner, and remote creates cannot assign a different owner;
  `src_port=0` remains reserved for trusted WM-local actions. Hosted
  maximize/restore no longer bypass the check.
- evidence: Focused unit coverage denies all nine remote lifecycle mutations,
  preserves the victim window, covers the generic compositor, and proves the
  hosted maximize/restore bypass is closed. Scoped static validation passes;
  executable evidence remains target-compiler-blocked and was not rerun.
- constraint: Do not bootstrap or change the compiler unless a confirmed
  compiler defect prevents producing/running the target browser binary.
- security/origin isolation: Split the displayed/navigation `current_url` from
  the committed `document_url` security principal. Relative page requests,
  form actions, Fetch/CORS/CSP/mixed-content checks, cookie mutation, and Web
  Storage persistence now derive authority from the committed document.
  Cross-origin `history.pushState`/`replaceState` targets are rejected without
  changing URL, history, state, cookie, or storage authority.
- evidence: Focused fail-fast coverage attempts location/history origin
  planting, proves the attacker origin receives no planted cookie or storage,
  and proves the originating document retains its own writes. Runtime evidence
  remains target-compiler-blocked and was not rerun.
- security/CSP redirects: Active style, classic-script, module, Wasm, and Fetch
  redirects now re-evaluate the committed document's applicable CSP directive
  against every normalized/HSTS-upgraded target before another request is
  queued. HTTPS downgrade, redirect count, and origin checks remain layered.
- evidence: Focused fail-fast coverage starts same-origin style/script loads
  under `style-src 'self'; script-src 'self'`, redirects both to a hostile
  origin, and requires zero redirected requests plus explicit CSP errors. The
  mirrored security manual now covers all 20 scenarios. Runtime evidence
  remains target-compiler-blocked and was not rerun.
- hosted pointer/text events: The production hosted session now owns one
  pressed semantic target, emits pointerdown/mousedown and pointerup/mouseup,
  and clicks only when press and release resolve to the same target. DOM text
  input follows the actually focused element in the focused WM window and
  appends committed text chunks instead of replacing the value or following
  the current pointer.
- evidence: The hosted integration scenario now rejects release-only and
  abandoned presses, accepts one matching checkbox press/release through the
  canonical Engine2D frame, and appends `"A"` plus `"da"` to focused input.
  Its mirrored four-scenario manual was refreshed by hand because docgen and
  runtime remain target-compiler-blocked.
- hosted keyboard events: Native key press/release edges now route to the
  actually focused DOM target before bare WM actions. The canonical
  BrowserSession dispatch emits keydown/keyup and reuses Enter/Space
  activation defaults; F11 remains host-reserved. Text commits no longer
  overwrite the trusted WM window title.
- evidence: The hosted integration scenario delivers W down/text/up to a
  focused input and Space down/up to a focused checkbox, requiring listener,
  value, focus, and click-default mutations. The mirrored five-scenario manual
  was refreshed by hand; runtime remains target-compiler-blocked and was not
  rerun.
- sandbox audit: AC-7 remains open. Hosted WM still constructs BrowserSession
  and reparses hostile HTML/CSS in-process. Existing piped-process and Rust
  sandbox helpers are not fail-closed production isolation. The retained
  implementation plan requires a cached native renderer, READY-after-sandbox
  handshake, bounded typed IPC/Draw IR, Linux no-new-privs + Landlock + seccomp
  + rlimits, and no in-host hostile parser/render path. This necessarily
  touches the native runtime/build lane, so it was not started under the
  no-bootstrap constraint.
- trusted hosted browser chrome: The production WM now paints Back, Forward,
  Stop, Reload, Home, Favorite, and Address in its own Draw IR/window-chrome
  batch, reserves a separate page rectangle below it, and routes toolbar
  coordinates before hostile DOM hit testing. Address text and Enter/Backspace
  use the existing BrowserSession UI-access actions; matching press/release is
  required, and favorite mutations persist immediately through the profile
  owner. Page CSS and script pixels remain a single provenance-checked web
  frame and cannot overlap the trusted toolbar.
- evidence: The hosted integration spec now checks exact toolbar/page geometry,
  hostile-control non-interference, address edit/submit behavior, canonical
  Engine2D presentation, and a real white address-field pixel. Its mirrored
  six-scenario manual was refreshed by hand. Runtime evidence remains
  target-compiler-blocked and was not rerun.
- HTTPS timeout hardening: The rustls client now shares a five-second deadline
  across resolved connect attempts and installs five-second read/write socket
  deadlines before the eager authenticated handshake. Read errors/timeouts
  invalidate the TLS handle, and H1 treats the failed close as a transport
  error so partial EOF-framed bytes cannot be committed as a successful
  response.
- evidence: A deterministic loopback runtime unit test checks the actual client
  socket read/write deadlines. Scoped whitespace, conflict-marker, direct
  runtime-access, and spec-layout gates pass. Whole-file rustfmt remains WARN
  because `net_tls.rs` has pre-existing formatting drift; the test was not
  executed because target runtime/compiler execution remains blocked and no
  bootstrap was run.
- sandbox IPC hardening: Linux renderer seccomp now denies the complete direct
  System V shared-memory, message-queue, and semaphore syscall families,
  including the multiplexed `ipc` entry used by older architectures.
- evidence: The focused live containment child enters Landlock/seccomp, is
  denied access to parent-created shared memory, message queue, and semaphore
  objects, writes stdout/stderr noise, and exchanges only the bounded protocol
  response over inherited fd 0. No bootstrap or Simple compiler command ran.
- network origin hardening: FetchEngine now enforces `SameOrigin` before cache
  or transport and validates cached responses against the active CORS policy,
  preventing a prior `NoCors` cache entry from satisfying a later cross-origin
  `Cors` request without matching response authorization. The legacy hosted
  adapter binds the retained FetchEngine to BrowserSession's committed
  document origin before each request.
- evidence: Focused regressions cover forged cross-origin `SameOrigin` and
  `NoCors`-prime/`Cors`-read cache bypasses. LSP diagnostics remain unavailable
  because source-mode diagnostics deadlock on the known `simple check` spawn;
  no compiler/bootstrap command was retried and no executable PASS is claimed.
- broker navigation authority: Document fetches now fail closed unless their
  canonical URL, method, sanitized headers, body, and content type consume one
  exact parent-issued permit. Resource mode is derived from the broker's
  committed origin; renderer-supplied kind can no longer select `Navigate` or
  `NoCors`. Redirect permits apply method rewrite, cross-origin header
  stripping, HTTPS-downgrade denial, and the 20-hop cap.
- evidence: Added focused broker-policy scenarios for missing/mismatched
  navigation permits, canonical HTTP(S) permit issuance, same-origin resource
  mode, simple CORS mode, and preflight-required denial. Executable evidence
  remains target-compiler-blocked; no bootstrap or compiler retry ran.
- sandbox syscall hardening: Linux renderer seccomp now rejects legacy path
  metadata and xattr enumeration, modern mount and io_uring operations,
  cross-process memory advice, and kernel-control calls while retaining
  descriptor `fstat` for protocol IPC.
- evidence: The standalone native containment runner compiles with
  `-Wall -Wextra -Werror`, proves representative denials return `EPERM`, and is
  wired into the focused GitHub browser-renderer sandbox workflow. No Simple
  compiler or bootstrap command ran.
- HTTPS evidence: Focused `simple-runtime` Rust tests prove the platform trust
  verifier initializes and the TLS client socket installs positive bounded
  read/write deadlines. These tests do not replace the still-open live
  certificate identity matrix.
- HSTS parsing: `max-age` now accepts ASCII digits only, so malformed signed
  values such as `-1` are ignored before policy mutation instead of clearing a
  valid policy while valid `max-age=0` still clears it. The focused
  BrowserSession scenario and mirrored manual cover both outcomes; executable
  Simple evidence remains compiler-blocked and was not rerun.
- HSTS response ordering: The trusted broker now learns STS from every
  successfully authenticated HTTPS response before CORS exposure filtering,
  including 4xx/5xx responses. Only the completed rustls job supplies
  authentication provenance; plaintext and synthetic/mock responses cannot
  install policy. Focused broker scenarios and a mirrored manual cover CORS
  denial, 404, HTTP, and untrusted HTTPS; executable Simple evidence remains
  compiler-blocked and was not rerun.
- HSTS durability: The hosted parent now saves dirty HSTS state immediately
  after broker polling and before frame processing, clears dirty state only
  after the SQLite transaction succeeds, retries transient failures at a
  bounded one-second cadence, and retains the shutdown retry. The focused
  entry-owner contract and mirrored manual cover ordering and retry state;
  executable Simple evidence remains compiler-blocked and was not rerun.
- Browser close lifecycle: Titlebar, KEY_W, direct evidence close, and evidence
  left-button closes now save HSTS/profile state before destruction, reject
  failed persistence while retaining the window, then reconcile renderer,
  raster, profile, and external-frame ownership. The compositor owns the exact
  release-inside close hit test shared by native/evidence input. Static source
  evidence covers all routes; executable Simple evidence remains compiler-
  blocked and was not rerun.
- Renderer process close status: `HostedBrowserRendererProcess.close` now
  returns the native piped-process close result, retains the PID on failure for
  one bounded hosted-WM shutdown retry, but clears a PID already reaped by a
  liveness check. The unused one-shot wrapper was removed because it could not
  return retained process ownership after cleanup failure. Successful mid-loop
  close returns zeroed renderer/raster owners. Runnable policy coverage and
  the source contract were updated; executable Simple evidence remains
  compiler-blocked.
- HSTS URL canonicalization: BrowserSession now validates and normalizes
  explicit HTTP candidates before navigation-permit policy matching, so
  mixed-case schemes/hosts are covered without repairing bare or malformed
  inputs. Upgrade maps port 80 to HTTPS 443 and preserves other explicit
  ports. Existing HSTS security coverage now asserts positive and negative
  cases.
- Remaining HSTS subresource blocker: A broker-only URL rewrite was rejected
  in review because the worker still correlates the original HTTP request.
  Production completion requires carrying both original and effective URLs
  (or synchronized HSTS state) across the renderer protocol, with strict
  same-host/path and port-transition validation.
- HSTS subresource broker fix: The trusted broker now applies persisted HSTS
  before mixed-content/origin policy and represents a changed transport URL as
  an internal 307 response. The worker's existing redirect path correlates a
  fresh HTTPS request and reruns CSP/CORS policy, avoiding silent URL
  substitution and a wider IPC schema. Exact host/path/query and port
  transition checks reject forged effective targets. Redirect `Location`
  headers are HSTS-upgraded before renderer delivery, and STS is stripped
  after authenticated broker learning so mock/cache responses cannot create
  worker-only policy. Isolated workers defer broker-owned network admission
  only for HTTP candidates under a secure document; a missing policy is
  rejected as mixed content, while an effective HTTPS redirect is rechecked
  against CSP before the correlated request is emitted. The internal upgrade
  marker is stripped from remote responses, preserves fetch method/body/headers
  without consuming the HTTP redirect budget, and recomputes Secure cookies for
  the HTTPS target. Plain HTTP documents retain normal local CSP enforcement.
- Credential-free CORS response hardening: FetchEngine no longer stores
  Set-Cookie when request credentials are `omit`. The hosted broker strips
  Set-Cookie/Set-Cookie2 and filters cross-origin response headers to the CORS
  safelist plus valid explicitly exposed names before renderer IPC, retaining
  Location only for an internal redirect hop.
- Persisted HSTS host hardening: BrowserSession and BrowserProfileStore now
  reuse the strict navigation DNS-label validator for header admission,
  snapshot restore, database load, and transactional save. Whitespace,
  userinfo, ports, empty/overlong labels, and leading/trailing hyphens are
  rejected alongside public suffixes and IP literals. Profile load also drops
  every case-folded duplicate host so corrupt SQLite rows cannot choose policy
  metadata by collation order.
- Renderer filesystem-mutation containment: Linux seccomp now denies chmod,
  chown, timestamp, and truncate syscall families independently of Landlock
  ABI coverage, including fd and legacy variants. The live native sandbox
  child attempts chmod, truncate, and utimensat against a parent-created owned
  file; the focused harness passes and proves its mode, size, and timestamp
  remain unchanged. No bootstrap or Simple compiler command ran.
- CORS request provenance: The trusted renderer broker now rejects a
  renderer-supplied `Origin` header and adds exactly one canonical committed
  document origin to every admitted simple cross-origin request. Focused
  request-wire coverage proves the trusted value is serialized and a forged
  value is denied; executable Simple evidence remains compiler-blocked and was
  not rerun.
- Simple Script/JavaScript DOM interop: Replacing body text or HTML from Simple
  Script now rebinds the JavaScript element bridge to the new canonical DOM;
  JavaScript body replacement also refreshes the bridge for later callbacks.
  The focused
  BrowserSession, hosted-session, and five-frame fixture now require rAF to
  select and style the exact element created by Simple Script, producing
  distinct red and blue Engine2D pixels. Executable Simple evidence remains
  compiler-blocked and was not rerun.
- JavaScript same-callback DOM synchronization: Body `innerHTML`/`textContent`
  assignment now calls a browser-installed, bounded mutation-plan hook from one
  shared dot/computed property writer. The executing interpreter atomically
  publishes the replacement element bridge before assignment returns; the
  browser later adopts that exact bridge receipt instead of rebinding away
  object identity, then applies same-callback style deltas to canonical DOM.
  Rejected element-count/resource/aggregate-snapshot plans are deterministic
  no-ops that retain the prior body and bridge rather than falling through to
  deferred unbounded parsing.
  Focused animation evidence replaces/query/styles green in one rAF, preserves
  identity into the next rAF, exercises computed `body['innerHTML']`, and
  requires distinct green/blue Engine2D pixels. Executable Simple evidence
  remains compiler-blocked and was not rerun, so runtime confirmation is still
  pending.
- Secondary browser chrome routing: Hosted pointer, address text/key, Back,
  Forward, Stop, Reload, and Home events now route by toolbar `window_id`
  through that window's `HostedWebContentSession`; only the primary external
  renderer touches the primary globals. Address/title and body refreshes follow
  the same per-window receipt, and keyboard dispatch now returns the actual
  post-event focused DOM id instead of an undefined value. Focused two-window
  evidence preserves the first window while address navigation and Back mutate
  the second; executable Simple evidence remains compiler-blocked and was not
  rerun.
- Secondary Favorite persistence: The hosted-window registry now owns a
  bookmark-only profile handle and production enables it only for browser
  windows. The primary external browser remains the sole HSTS owner, so
  secondary shutdown cannot replace a concurrently saved HSTS snapshot.
  Bookmark load/toggle failures remain fail-closed and restore the prior
  in-memory state. Multi-window and file-backed restart/failure evidence was
  added; executable Simple evidence remains compiler-blocked and was not rerun.
- Atomic Favorite persistence: BrowserProfileStore now applies one validated
  URL-key toggle transaction instead of replacing the bookmark table. The
  transaction acquires the SQLite write lock before reading current state and
  returns the committed enabled value, so separate handles cannot decide from
  stale snapshots. Primary and hosted-session owners render that returned
  state; the hosted owner restores its prior snapshot and mutation revision
  when persistence fails. Favorite no longer couples a bookmark commit to an
  unrelated HSTS snapshot write. File-backed evidence uses two handles to add
  distinct URLs, remove one, and alternately toggle one shared URL without
  losing the unrelated row; a closed-profile failure retains no in-memory
  favorite. Executable Simple evidence remains compiler-blocked and was not
  rerun.
- Renderer IPC assembly performance: The shared bounded decoder now retains
  incoming protocol fragments and joins them only after the declared frame is
  complete. Parent startup, hot frame/network polling, and sandboxed worker
  input therefore avoid the former growing `buffer + chunk` copy on every
  8 KiB read (about 64 MiB of transient copying for a legal 1 MiB frame).
  Maximum-payload fragmentation evidence also preserves a trailing second
  frame and request ordering. Executable Simple evidence remains
  compiler-blocked and was not rerun.
- DOM target event order: The canonical event-path dispatcher now invokes
  target capture listeners before inline and non-capture target listeners.
  `stopPropagation` still permits remaining listeners on the same target,
  while `stopImmediatePropagation` suppresses them. Focused approved-matcher
  coverage proves ordering and same-target propagation; executable Simple
  evidence remains compiler-blocked and was not rerun.
- Production static-frame reuse: Session-assigned `ui-session-*` Draw IR
  identities no longer disable the existing unchanged-state pixel cache.
  Submission identity still advances for input replay protection while stable
  UI state reuses the prior framebuffer, avoiding repeated full-frame
  allocation and lowering. Focused session-path counter coverage and its
  manual were updated; no runtime/performance PASS is claimed because the
  compiler retry cap remains exhausted.
- Production subprocess animation evidence now starts the exact native
  `HOSTED_WM_ARTIFACT`, renders an initial CSS/Script/JavaScript frame, advances
  the renderer clock, and compares both Engine2D pixel buffers through one
  persistent raster backend. It was not executed because the compiler retry
  cap remains exhausted.
- Platform-sandbox evidence now requires the same exact hosted-entry artifact,
  completes the renderer ready/frame protocol, and closes fail-closed. It was
  not executed because the compiler retry cap remains exhausted.
- Both subprocess scenarios verify the artifact against the SHA-256 admitted
  by the existing hosted live-window evidence wrapper before launch, and the
  animation timeout closes both the renderer and persistent raster backend.
- TLS certificate identity remains blocked by the absence of a fixture-CA and
  loopback seam in the production broker. GC/RSS/soak budgets remain explicit
  failures; unchanged-frame counters alone are not production budget evidence.
- Hosted structured UI evidence now drives address entry, Enter navigation,
  Back, and Forward through `HostedWebContentSession` and proves red/blue
  HTML/CSS raster transitions. It is hosted-owner evidence, not an installed
  production-binary claim.
- Renderer lifecycle evidence now starts the admitted sandbox worker, renders
  a real frame, closes it under a monotonic bound, and proves its PID is dead.
  RSS, GC, soak, and Engine2D/font lifecycle budgets remain explicit failures.
- The hosted live-window wrapper now runs the focused animation, sandbox, and
  lifecycle specs after source-manifest/artifact admission and records their
  statuses. No admissible current target runner/artifact pair exists, so these
  scenarios were not executed in this session and no production PASS is claimed.
- Hosted form-control evidence now proves pointer targeting, focus, key edges,
  text input, DOM event state, and a CSS-driven red-to-blue pixel transition.
- Production broker evidence now rejects `file:///etc/passwd` as
  `invalid-navigation` before issuing a renderer command and closes the worker.
- The canonical wrapper now also runs the focused controls and scheme-denial
  scenarios and makes all five focused-spec statuses release-blocking. Its
  unchanged-frame receipt requires stable render revision, checksum, backend,
  readback source, backend handle, and captured pixels.
- TLS fixture authority remains blocked: a safe seam must be feature-gated,
  literal-loopback-only, use a bounded DER root with normal hostname/time
  verification, and add conditional ABI/security classification outside the
  current two-file lane. No TLS runtime changes or weaker verifier were added.
- Static subprocess evidence now proves CSS cascade, positioned layout, Draw IR
  text, no Engine2D fallback, deterministic blue pixels, and no animation timer.
- Browser HTTP job imports now classify at the runtime security choke point as
  `Network`; the focused Rust regression passed (1 test, 0 failures).
- Hosted rejected-navigation evidence now covers invalid address submission,
  stale chrome release, matching Stop, rejected late commit, and unchanged
  prior pixels without a fabricated native job handle.
- Renderer lifecycle evidence now repeats 32 admitted subprocess generations
  and rechecks every PID dead. The wrapper records cycle count 32 and makes all
  seven focused scenario statuses release-blocking.
- Production HTTPS identity remains blocked, but a narrower private Rust unit
  seam can test literal-loopback rustls identity with inline DER and no runtime
  ABI. That test has not yet been implemented; production trust remains unchanged.
- Hosted navigation evidence now separately proves synchronous Reload, a
  registered Home target, pointer-hit page-link navigation, and profile-backed
  Favorite through the real in-memory SQLite bookmark store. The wrapper runs
  and release-gates all ten focused scenarios.
- The 32-cycle renderer lifecycle gate now samples host and renderer `VmRSS`
  and `VmHWM` directly from `/proc`, records sampled combined RSS and a
  conservative summed-HWM upper bound, and requires both below 384 MiB. The
  required 60-minute RSS plateau and production GC-pause evidence remain open.
- Security audit found a Linux pre-exec isolation window before the worker
  installs Landlock/seccomp. The release blocker and trampoline acceptance
  probe are recorded in
  `doc/08_tracking/bug/browser_renderer_linux_pre_exec_sandbox_gap_2026-07-28.md`.
- Node/native denial remains unobservable in the admitted worker protocol:
  script parse/load warnings are not returned with frame evidence, so no
  ambiguous unchanged-frame assertion was added.
- Hosted default-action cancellation now proves capture, target, and bubble
  order, `prevent-default`, no pending POST navigation, and unchanged body and
  pixels after a real pointer activation. The wrapper release-gates all eleven
  focused browser scenarios.
- Private runtime-TLS unit evidence now uses literal-loopback rustls fixtures:
  trusted `localhost` succeeds, the same CA with a wrong-host certificate is
  rejected, and an empty root store rejects the localhost certificate. The
  focused Rust run passed 3 tests; production platform trust is unchanged and
  live broker HTTPS evidence remains open.
- Linux pre-exec sandboxing remains open: applying the existing deny-all
  Landlock/seccomp worker policy before `exec` would also block the renderer,
  ELF loader, and shared libraries. No unsafe partial fix was added.
- The hosted target uses explicit allocation and reclamation rather than an
  active collector, so GC pause/count claims remain unsupported. Future honest
  telemetry must report allocated, reclaimed, and current registered objects
  and bytes through the existing heap/runtime ownership paths.
- Document commits now reject an explicit MIME other than normalized
  `text/html`, including an empty malformed MIME, after applying security
  response headers but before replacing the document. The focused hosted
  scenario requires both rejection errors and unchanged prior body/pixels.
- Renderer frame protocol SBRF3 now carries bounded diagnostics while decoding
  legacy SBRF2 frames. The worker reports actual BrowserSession runtime
  diagnostics; the admitted Node/native scenario requires all five hostile
  scripts to fail and `require`, `process`, and `Buffer` to be `undefined`.
  The live wrapper release-gates thirteen focused browser scenarios.
- The Linux pre-exec audit identified an ELF `DT_PREINIT_ARRAY` stage-one seam:
  dependencies are mapped before constructors, allowing deny-all Landlock plus
  a startup-safe network/fork/exec seccomp filter without loader allowlists.
  A full-policy prototype still failed the bounded native gate after three
  cycles and was reverted; the open bug now records the split-policy resume.
- Honest allocation telemetry still requires one coordinated ABI change across
  Rust `std::alloc` collections/heap ownership and generated C `calloc/free`.
  Existing heap-registry counts and disabled/unlinked memtrack paths cannot
  support runtime-byte or reclamation claims, so no misleading counters landed.
- Hosted native-control evidence now exercises checkbox and radio state plus
  input/change callbacks, select focus, textarea beforeinput/input, and a real
  successful POST form submission containing checkbox, radio, select,
  textarea, and submitter values. The live wrapper release-gates this flow.
- Production protocol evidence now starts and initializes the admitted worker,
  rejects a 4,097-byte text action at the 4,096-byte host encoder boundary,
  and closes cleanly. Malformed, late, and duplicate injection remain open.
- CSP host sources with paths no longer widen to the entire matching origin:
  slash-terminated sources use path-prefix matching, other non-root paths match
  exactly, and root remains origin-wide. Focused BrowserSession evidence blocks
  `/evil.js` while dispatching `/allowed/app.js` under one policy.
- Production broker TLS identity is still not locally injectable: public-only
  address admission rejects loopback before TLS and the real path then uses
  immutable platform trust. The private rustls identity tests remain the
  strongest safe local proof without adding forbidden runtime authority.
- Honest NFR-003/NFR-004 latency completion still needs changed-frame timing,
  every required input class, and percentile aggregation. The current receipt
  proves one event/revision-bound input-to-present sample and real counters.
- Cookie responses without a valid explicit Path now derive the RFC directory
  path from the response URL; focused evidence sends `/account/login` cookies
  to `/account/next` but not `/public`.
- Hosted Tab and Shift+Tab evidence now binds focus/blur callbacks, semantic
  targets, DOM attributes, and changed pixels. Wheel remains open because the
  compositor route has no page semantic target or BrowserSession scroll state.
- The hosted receipt now captures the platform-event ingress clock, retains it
  only for the same accepted semantic event, and records completed-present
  clock, exact delta, event/revision binding, real present count, and skipped
  frames. The wrapper gates one sample at 50 ms; no percentile/FPS claim is made.
- Dedicated parent-only fault commands now crash or stall an initialized
  admitted worker, exercising the existing renderer-crashed/renderer-timeout
  cleanup path and proving a fresh admitted renderer can restart afterward. A
  correlated worker acknowledgement prevents an unconsumed hang command from
  passing as a timeout.
  Page content cannot access the parent-to-worker command channel. Memory
  exhaustion and restart-rate budgets remain open.
- BrowserSession now routes storage, attachment, HttpOnly, SameSite,
  credentials, and redirects through the bounded canonical CookieStore.
- Current live verification is blocked before browser execution: the isolated
  deployed pure-Simple compiler segfaults in both hosted `native-build` and
  `check src/lib`. No bootstrap fallback was used; HTML/CSS, JavaScript/CSS
  animation, and the new fault scenario therefore remain unexecuted this run.
- The essential compiler repair now defers glob/package-sibling trait-default
  lowering until an actual impl needs it; explicit imports retain their prior
  behavior. An isolated Stage 3 diagnostic emitted 695-709 current-source
  objects without HIR/type failure, then stopped at the minimal core-C link
  boundary. A full admitted CLI and measured Stage 4 memory receipt remain
  required before browser verification resumes.
- JavaScript timer draining no longer retains canceled-ID tombstones or
  completed timer lookup rows. Overdue intervals coalesce to one callback per
  clock advance; self-clear and completed-handle refresh preserve metadata and
  timing. Focused runnable specs cover the lifecycle, but could not execute.
- Browser history now trims stale forward entries and retains at most 64
  newest entries within the existing 50 MiB resource budget on push paths.
  Reload replacement remains deliberately bounded by two resource budgets.
- One isolated, cargo-disabled pure-Simple compiler refresh was essential
  because both admitted self-hosted compilers lacked the committed multiline
  condition parser fix. It failed once at Stage 2 linking on missing
  `rt_index_of` and `rt_file_is_regular_no_follow`; no retry or broader
  bootstrap was attempted. Fresh HTML/CSS/animation pixels remain blocked.
- Body DOM publication now preserves the canonical body node, author id,
  classes, inline style, and JS body/style objects across `innerHTML` changes.
  Focused rAF coverage requires same-callback selectors, canonical HTML, CSS
  color pixels, and a changed frame; execution remains compiler-blocked.
- Browser-mode timers now return scalar web timer IDs before Node handle
  allocation, so discarded animation frames add no handle objects. Node mode
  keeps its refresh/ref/unref handle semantics. Runtime creation also removed
  one redundant synthetic DOM publication before the authoritative bind.
- Linux renderer stage one now enters from ELF preinit for the broker-fixed
  argv and empty environment, before constructors. It applies no-new-privs,
  deny-all Landlock, and startup-safe socket/fork/clone/exec seccomp; the
  focused production-spawn constructor probe passed on verification cycle 2.
  Full admitted renderer execution is still required before closing the bug.
- Native select UI access remains open after three bounded fix/review cycles:
  duplicate author ids still collided at the select-owner target seam. The
  unverified select patch was removed rather than shipping ambiguous control
  mutation; existing focus-only evidence remains the current boundary.
- Navigation: Hosted secondary-window address Backspace now removes one
  validated UTF-8 scalar through the shared encoding owner. The same helper
  replaces duplicate worker, parent-entry, and BrowserSession deletion logic;
  a pure-Simple stage-2 diagnostic probe printed
  `BROWSER UTF8 BACKSPACE PROBE: PASS`. Stage 2 is not release evidence, so the
  hosted scenario remains pending a genuine full CLI.
- Events: The shared BrowserSession user-edit owner now enforces HTML
  `maxlength` after cancelable `beforeinput`, measures UTF-16 units without
  splitting UTF-8, preserves middle-edit suffixes and the accepted caret, and
  enables the already-supported textarea mutation branch. Hosted evidence
  covers an astral character plus canceled input. A bounded pure-Simple
  Stage-2 diagnostic accepted the changed sources, then stopped at the known
  `JsValue.Symbol` MIR blocker before execution; no production PASS is claimed.
- Performance: `script_host_apply_action_to_id` now stops at the first
  preorder DOM identity and path-copies only the matching node's ancestors.
  Missing targets return the original tree, later siblings are not traversed,
  and intentional full-tree default actions remain unchanged. This removes
  the two full-DOM clone/allocation passes previously paid by every accepted
  text edit; focused coverage locks first-match, untouched-sibling, and
  missing-target behavior. Executable production timing remains
  blocked by the recorded `JsValue.Symbol` compiler defect.
- Parsing/performance: the tokenizer now discards later case-insensitive
  duplicate attributes and preserves the first value, matching the HTML
  tokenizer contract before tree building, script metadata scans, DOM Dict
  writes, selector matching, or control processing. A focused token-level
  regression locks both uniqueness and first-wins semantics; execution remains
  blocked by the recorded compiler defect, and no bootstrap retry was made.
- Parsing/performance: the HTML tree builder now owns one preallocated private
  open-node stack and mutates it through indexed leaf operations. Append and
  close clear the stored parent before growing its child array, removing both
  repeated stack rebuilds and the sibling COW alias while preserving DOM order
  and public APIs. Fixed 512-slot storage flattens excess nesting without
  dropping nodes, repairing the existing depth scenario without token-count
  preallocation. The separate 65,536-node quota remains missing, and runtime
  timing is still compiler-blocked.
- Layout/performance: percent-height, flex-stretch, and absolute-position
  resolution now pass one node-local `Style` into recursive layout instead of
  cloning the full style table at nine production call sites. This removes
  O(N*K) temporary reference writes/allocation (O(N^2) in the affected worst
  case) while keeping the base table for every descendant. Existing geometry
  probes cover percentage and absolute sizing; execution remains blocked by
  the recorded `JsValue.Symbol` compiler defect, so no bootstrap retry was made.
- Events: the isolated hosted renderer now preserves DOM focus after clicking
  a native non-text control while clearing only its text-overlay/caret state.
  A focused worker scenario clicks a checkbox, proves focus survives, and then
  activates it with Space through the production keyboard route.
- Open security finding: secondary `app_id == "browser"` windows still route
  through in-process `HostedWebContentRegistry` and can evaluate page script in
  the parent instead of owning a `HostedBrowserRendererProcess`. This violates
  REQ-WEB-BROWSER-014 and needs a per-window broker registry (or a temporary
  fail-closed refusal); it is not accepted as production-complete.
- Runtime boundary decision for per-window renderers:
  `runtime_need=multiple independently sandboxed browser processes`;
  `facade_checked=HostedBrowserRendererProcess already uses the canonical
  rt_browser_renderer_spawn_sandboxed facade, whose private runtime slot is a
  singleton despite the bounded 16-entry process table`;
  `chosen_path=runtime-owned-change`;
  `rejected_shortcuts=in-process secondary sessions, disabling sandboxing,
  raw app-local process aliases, and multiplexing hostile pages in one worker`.
- Runtime/process prerequisite candidate: atomically reserves a concrete
  process-table row, publishes its PID last, rolls back every spawn failure,
  and limits renderers to four so other process users retain headroom. The
  focused C regression failed at sandbox case exit 9 before the fix, then
  passed while proving two resident sandbox PIDs, independent close/liveness,
  containment, and basic reuse. No Simple compiler or bootstrap was used.
- Independent lifecycle and test reviews accepted the foundational two-window
  contract and statically verified the dedicated four-renderer cap, atomic row
  reservation, failure rollback, and idempotent release. A future cap-policy
  change should add a four-live/fifth-rejected saturation case; no general
  concurrent process-API safety claim is made.
- Remaining security/lifecycle work: hosted secondary-browser state is still
  in-process; the renderer registry and fail-closed browser classification
  remain active and unverified.
- Compositor lifecycle/performance: replaced its singleton external frame with
  four receiver-indexed window/frame slots. Admission now requires a live
  window, exact content geometry, positive revision, trusted provenance and
  checksum, with a 16,777,216-pixel aggregate retention cap. Resize empties the
  affected stored frame, destroy removes only that window, and render no longer
  rescans every accepted frame just to rewrite its checksum. Primary hosted
  close paths release by window id instead of clearing all slots.
- Evidence: added a focused real Engine2D raster scenario for two distinct
  trusted frames and close-one/keep-one behavior, plus refreshed hosted source
  contracts and architecture/operator docs. It is not executable in this
  workspace: `bin/simple` is absent, `bin/release/simple` rejects the deployed
  pure-Simple runtime's test ABI, `bin/simple_native --version` exits 139, and
  the default checkout exposes only the forbidden Rust seed. No bootstrap or
  seed fallback was used; executable/manual generation remains pending.
- Security boundary remains open: secondary browser windows still use
  `HostedWebContentRegistry` in the parent. The compositor prerequisite is
  feature-preserving and does not yet classify every browser window as
  external; enable that fail-closed rule only with the per-window renderer
  registry so multi-window behavior is preserved rather than disabled.
- Security/lifecycle: secondary `app_id == "browser"` windows now own bounded,
  window-keyed `HostedBrowserRendererProcess` and persistent Engine2D raster
  entries. Startup/READY/init, network completion, resize, input, navigation,
  animation, frame publication, destroy reconciliation, and shutdown route
  through that owner; close explicitly cancels/frees broker HTTP state, reaps
  the child, and shuts down the raster instead of relying on BrowserSession GC.
- Performance: renderer startup no longer sleeps in the WM thread. `begin_start`
  and `begin_init` queue work, while the registry performs at most one broker
  poll per window per host tick. Minimized windows still poll cleanup/deadlines
  but do not schedule resize or animation raster work.
- Fail-closed boundary: the compositor renders a blank external frame for every
  browser window lacking an admitted frame, including capacity/start/crash
  failures. Browser input is classified by the compositor window owner, so an
  unadmitted browser cannot fall back to the parent `HostedWebContentRegistry`.
- Verification: focused source contracts were updated; SPipe wiring and both
  direct env/runtime guards pass. Live Simple/JS/CSS/animation execution and
  docgen remain unavailable for the already-recorded admitted-CLI failures; no
  bootstrap or Rust seed fallback was used.
- Leak/perf review fixes: dead renderer detection now retains the PID until the
  canonical piped-process close frees its table row and file descriptors;
  stable-window reconciliation returns without rebuilding entry arrays;
  rejected compositor frames tear down their renderer/raster; repeated frame
  admission is idempotent. Pointer cancellation tracks one armed window and
  queues an empty-target release for that renderer only, never a cross-window
  synthetic press broadcast.
- Memory/performance: repeated CSP, cross-origin, navigation, and form denials
  now share one duplicate-suppressing warning owner capped at 128 entries and
  4096 characters per entry. Sandboxed animation frames build only the bounded
  4096-character diagnostic prefix instead of joining the entire warning
  history before truncation, removing unbounded retention and reducing
  per-frame scan/allocation work.
- Renderer failure lifecycle: a failed live child close now retries at a
  one-second cadence instead of leaving its PID/pipes indefinitely retained.
  Successful close resets decoder, Fetch/DNS/cache, and history state held by
  the fail-closed tombstone while retaining learned HSTS for persistence.
  Liveness-observed dead children clear the handle already consumed by the
  process facade; only genuine close failures retain ownership for retry.
- Compositor window destruction now releases every window-keyed render owner:
  external frame pixels, wheel offsets, hosted pixel caches, and native pixel
  caches. Previously, every destroyed rendered window could retain a full
  cached frame for the compositor lifetime; the focused regression renders,
  scrolls, closes, and asserts the native/hosted caches and offset are empty.
  The same lifecycle owner clears matching drag, resize, and armed-chrome state
  so programmatic close cannot leave a stuck interaction.
- Wheel input over renderer-owned browser windows no longer records a parent
  compositor offset or dirties an unchanged external frame.
- Sandboxed browser scrolling now routes primary and secondary content targets
  through one bounded, saturating per-renderer delta slot. The process encodes
  only while idle, preserving the discrete command/deferred slot; the worker
  preserves fractional trackpad deltas, clamps scroll to clipped document
  bounds, resets on committed documents, and renders the same shifted layout
  into Draw IR and its hit index. The host safely inverts the native wheel sign
  once. Ancestor-clipped and offscreen nodes are excluded from hit testing,
  Draw IR commands, and material witnesses before IPC budgets; the legacy
  software scroll path no longer inflates viewport height or changes
  `vh`/flex-fill semantics.
- Wheel-scroll verification: working/staged direct-env runtime guards,
  rendering source coupling, whitespace/artifact scans, and the
  `doc/06_spec/*_spec.spl == 0` layout gate pass. Two independent focused
  reviews pass. Live Simple unit execution remains unavailable for the
  admitted pure-runtime ABI failure; no bootstrap or Rust seed was used.
- Linux sandbox admission now fails unless the argv-bound ELF preinit hook
  activated stage-one Landlock/seccomp before constructors. The focused C
  subprocess gate proves an ordinary process cannot enter stage two, while the
  production spawn shape still completes pre-main denials and stage-two
  containment. The gate passes; installed pure-Simple READY/frame evidence
  remains compiler-blocked and no bootstrap or seed fallback was used.
- Engine2D override lifecycle now releases the globally retained full-frame
  pixel array on replacement, direct-render disable, and owning backend
  shutdown. A non-owner shutdown preserves the active owner's frame. Focused
  coverage checks both paths, closing the browser-raster teardown leak that
  could otherwise retain an 8K ARGB frame for process lifetime; executable
  Simple evidence remains compiler-blocked and was not rerun.
- requestAnimationFrame tasks now retain their task kind and replace the
  scheduled deadline with the actual render-opportunity time at dispatch. The
  focused browser-session regression advances directly to 33 ms and requires
  the callback to observe 33, preventing delayed-frame animation lag. Timer
  handle refresh preserves the frame kind and does not retain a stale arg.
- HTML parsing now caps both canonical BeDomNode creation and the independent
  direct-render HNode arena at 65,536 nodes. BrowserSession parses before
  clearing the active document and returns a stable `resource_limit` error on
  truncation; direct rendering safely paints only the admitted prefix.
- CORS response parsing now combines every matching header line before policy
  evaluation. Duplicate `Access-Control-Allow-Origin` values therefore fail
  closed in both response-body and preflight paths regardless of line order,
  while repeated list-valued method/header fields retain comma-list behavior.
- HTML tokenizer retention is now independently bounded at 262,144 content
  tokens and 65,536 unique attributes, with exact-limit/overflow signals folded
  into atomic BrowserSession admission. Direct render parsing reuses the 1 MiB
  renderer envelope and a 262,144-part structural cap before `split`/event
  allocation; rejected root-only results cannot enter split-heavy diagnostics.
- CSS extraction now applies the shared HTML source admission, dynamically
  sizes candidate storage, bounds both brace directions before splitting, and
  enforces the 4,096-rule quota across all style blocks. Valid prefix rules
  continue to render through software pixels and Draw IR under brace storms;
  rejected sources also skip keyframe extraction. Variable expansion is bounded
  to 1 MiB and 16 fallback levels; selector groups/parts and keyframe
  offsets/declarations are capped at 256.
