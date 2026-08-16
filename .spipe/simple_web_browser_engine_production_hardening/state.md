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
- independent input/focus and transient-bridge reviews pass after public target
  normalization and after keeping the NUL-prefixed internal route out of every
  serialized UI-access property/result.
- Native `select` controls now participate in BrowserSession UI access with
  revision-and-node-stable canonical IDs, effective selected values, exact
  internal routing, live value/disabled revalidation, and one atomic subtree
  rewrite followed by `input` then `change`. Page buttons/inputs/textareas/
  selects are collected in one DOM pass; option lookup is scalar and mutation
  is bounded to the target select plus its ancestor path. Disabled options and
  optgroups, missing values, duplicate author IDs, same-value idempotence,
  focus-time disabling, and stale document targets fail without cross-control
  mutation. Form submission now applies the same disabled-optgroup rule.
- verify: working/staged direct-env guards, rendering-source coupling,
  conflict-marker scan, and the `doc/06_spec/*_spec.spl == 0` layout gate pass.
  Input/event, security, and perf reviewers report PASS. The focused Simple
  system spec remains source-reviewed but unexecuted because the admitted
  pure-Simple CLI still crashes and the three-cycle compiler/build cap is
  exhausted; no bootstrap or Rust seed fallback was used.
- Navigation start/active-load Stop now disarm a pending Space-key activation,
  preventing keyup from clicking the preserved old document after a canceled
  navigation. No-op Stop retains valid input state. A focused unit regression
  covers both navigation boundaries and preserved-document behavior.
- HTTP cache freshness now distinguishes an absent `max-age` directive from
  explicit `max-age=0`; zero is immediately stale instead of falling through
  to the one-hour default, so reload/navigation cannot silently reuse stale
  HTML or CSS. A focused cache regression covers immediate lookup.
- remaining concrete perf/security follow-ups: fallback DOM-bridge rebinding
  allocates fresh JS host/list/style objects that the flat ObjectStore cannot
  reclaim within a document; repeated animated `innerHTML` replacement grows
  scans and retained rows. Navigation cancellation also drops queued/inflight
  fetch requests without rejecting the old document's promise registry, which
  can retain pending handlers until the bounded fetch limit. Stylesheet
  accumulation is capped per resource/count but not cumulatively, permitting
  excessive retained `current_style_html`. Owners: BrowserRuntimeState.bind_dom,
  BrowserSession navigation cancellation, and BrowserLoadState style append.
- verify: working/staged direct-env guards, rendering-source coupling,
  conflict-marker scan, and executable-spec layout gate pass; independent
  cache and input-event reviews pass. Focused Simple unit execution remains
  unavailable under the existing admitted-compiler crash/build-cycle cap; no
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
- Active document loads now apply the same duplicate-suppressing 128-entry,
  4096-byte warning cap at every script, module, WASM, stylesheet, and CSP append
  instead of retaining attacker-sized diagnostics until load finalization.
- Cached Back/Forward commits now reset the renderer-owned scroll position
  before painting the restored document; rejected navigation and Stop do not.
- Browser JavaScript timer cancellation, handle retirement, and dispatch now
  mutate the bounded pending-task arrays in place. The previous hot path
  allocated replacement arrays for every clear, refresh, and fired callback.
  Dispatch also stops scanning after the selected next-tick or due task while
  preserving interval self-cancellation and the 1,000-call drain yield.
- Before repaint, the hosted renderer releases the previous frame's full hit
  graph after deriving its overlay and caret state, then installs the new hit
  graph after rendering. Animated and scrolled documents no longer retain two
  O(document) layout graphs across the peak allocation window.
- Hosted bookmark clicks no longer load and rebuild an unused full-table
  snapshot before the transactional toggle. HSTS startup loading is independent
  of bookmark-table decoding, so a bookmark error cannot disable transport
  security state.
- Linux/FreeBSD hosted browser builds now have an opt-in OpenSSL TLS provider:
  platform trust, SNI plus DNS/IP service identity, TLS 1.2+, bounded numeric
  connect/read/write, SIGPIPE suppression, a 256-handle cap, and per-connection
  lifetime pins. The browser resolves once through its bounded DNS owner and
  passes the remaining request deadline into nonblocking connect/read/write;
  each operation polls against one absolute monotonic deadline, so trickled TLS
  records cannot reset the timeout. Runtime-owned
  DNS, TLS protocol, and TLS chunk strings are released after copying/use.
- Native C TLS evidence passes trusted localhost, wrong-host, unrelated-trust,
  stalled-read, read-cap, stale-handle, and peer-reset/SIGPIPE scenarios. The
  production fullscreen build requires the provider as a strong, fresh,
  SONAME-bearing dependency ahead of the generic runtime provider. No Simple
  compiler, bootstrap, or Rust seed was used for this evidence. A trickle-
  handshake regression was added and compiles cleanly but was not executed
  after the mandatory three-cycle verification cap.
- CSS selector-list specificity is now computed from matching branches only,
  with group specificity precomputed once and hostile comma lists sampled by
  the shared render budget. Computed-style and pixel regressions cover an
  unmatched high-specificity branch and multiple matching branches.
- Browser rAF/timer flushes now reconcile the DOM only after an observed DOM
  mutation generation changes. Title-only animation callbacks avoid the prior
  full DOM/property scan; direct style writes, `Object.assign`, repeated
  writes/deletes, `cssText` replacement/removal, body bridge changes, and both
  generation wrap paths retain repaint behavior in focused regressions.
- Real HTML/CSS/JS animation execution remains blocked: the third and final
  bounded bootstrap cycle passed Stage 2/3 and the former ModuleSurface
  promotion failure, then Stage 4 crashed with SIGSEGV immediately after
  releasing the first `src/app/cli/main.spl` surface. No executable browser
  PASS is claimed and the build was not retried.
- Text editing now dispatches `focus` only on an actual focus transition, so
  repeated keystrokes do not rerun authored focus handlers or force redundant
  JS/layout/repaint work. Busy address submissions preserve their draft/focus.
- Linux renderer stage-two seccomp now denies `fcntl`/`fcntl64`/`ioctl`, and
  the native sandbox gate proves inherited IPC cannot arm asynchronous owner
  signals against the broker.
- Web Storage persistence now drops empty buckets and retains at most 64 MRU
  origins / 16 MiB per storage kind, bounding unique-origin retention and its
  cumulative copy/scan cost. Focused specs cover count, MRU, empty, and byte
  eviction branches.
- Author `!important` declarations are split once at rule admission and cascade
  after all normal declarations, including inline normal style; exact pixel
  regressions cover specificity, inline precedence, case, and CSS whitespace.
- Browser rAF timestamps now use the current document time origin while timer
  deadlines remain on the absolute session clock, keeping late-navigation JS
  frames aligned with document-relative CSS animation.
- verify: working/staged direct-env guards, rendering-source coupling, conflict
  marker scan, and the `doc/06_spec/*_spec.spl == 0` layout gate pass. The
  deployed pure-Simple wrapper still fails its bounded test-ABI admission probe,
  so focused Simple specs remain source-reviewed but unexecuted; no bootstrap or
  Rust seed fallback was used.
- Worker frames now carry one bounded current/back/forward history snapshot;
  the broker validates same-origin state and broker-known cross-origin
  neighbors before atomically updating chrome. Parent Back/Forward use those
  neighbors, while the broker-owned network ledger remains the authority.
  BrowserSession, protocol, worker, and broker regressions cover push/push/
  replace traversal, bounded/malformed frames, exact emitted neighbors, and
  same-origin parent controls. The base64 wire snapshot is transient and
  capped at three 8192-byte decoded URLs; History API admission enforces the
  same bound, and broker network history retention now matches the worker's
  64-entry bound. Unchanged frames skip broker URL parsing, framing avoids a
  per-frame length vector, and retained state is replaced rather than appended.
- verify: direct-env working guard, conflict-marker scan, and
  `doc/06_spec/*_spec.spl == 0` pass. Target Simple checks remain unexecuted:
  the isolated workspace has no admitted pure-Simple CLI, and invoking the
  deployed artifact reached the prohibited seed/wrapper admission path, so it
  was stopped without bootstrap or seed fallback.
- BrowserSession's request FIFO now advances a queue head instead of copying
  every remaining request on each pop. A shared tombstone releases consumed
  URL/body references immediately, geometric compaction bounds dead slots,
  active-count and duplicate scans ignore consumed entries, and all navigation/
  stop/document-replacement paths reset the cursor. The 1024-request unit and
  runnable native probe assert FIFO order, no first-pop array copy, tombstone
  reclamation, the 512-entry compaction boundary, exhaustion, and storage reset.
- execution clarification: `release/x86_64-unknown-linux-gnu/simple`
  (`04a38e21...`) identifies as pure Simple, but `run`, `test`, and
  `native-build` currently SIGSEGV (139); `bin/release/.../simple` is a separate
  Rust seed and is not admissible. A no-bootstrap focused build with the pure
  Stage-3 compiler (`build/bootstrap/stage3/.../simple`, `a4d84871...`) first
  exposed and fixed the inherited parenthesized-multiline-`or` requirement in
  `BrowserSession.reload`, then stopped at the existing self-hosted parser
  Dedent bug in `security/origin_policy.spl:354` after the third/final bounded
  build cycle. No Rust seed or bootstrap was used. Resume after a current
  pure-Simple compiler is deployed with the recorded focused native-build
  command targeting
  `test/02_integration/app/browser/probe_pending_request_queue.spl`; owner:
  browser hardening merge owner; final reviewer: highest-capability Codex.
- DOM-backed UI access now routes links/buttons/inputs/textareas with the
  parser-assigned `node_id` instead of reusing author `id`. Duplicate author
  IDs therefore cannot redirect an action to the first matching element, while
  public DOM event IDs remain unchanged. The shared matcher accepts both legacy
  author IDs and exact internal routes, and script/default-action mutations use
  it without adding a DOM scan or retained index. A focused system regression
  edits the second of two duplicate-ID inputs and proves the first stays intact
  and only the second handler runs.
- verify: working/staged direct-env guards and rendering-source coupling pass;
  conflict/layout scans pass. The focused Simple system spec remains
  source-reviewed but unexecuted because no admitted working pure-Simple CLI is
  available, and the three-cycle compiler/build cap was already reached. No
  bootstrap or Rust seed fallback was used.
- Navigation and Stop now batch-remove every pending runtime fetch registry
  entry and reject its promise before discarded broker queues can retain old
  handlers. The O(n) drain replaces per-request registry rebuilding; the normal
  side-effect pump runs once after the replacement document is queued, keeping
  document ordering while exposing callback-created fetches. A focused async
  regression covers queued/inflight cancellation, exact-once catches, Stop,
  late-response rejection, preserved page state, and post-cancel recovery.
- verify: working/staged direct-env guards, rendering-source coupling,
  conflict/placeholder scans, and the `doc/06_spec/*_spec.spl == 0` layout gate
  pass. Executable Simple tests remain unrun under the recorded compiler crash
  and exhausted three-cycle build cap; no bootstrap or Rust seed fallback was
  used.
- Runtime fetch IDs now continue through the existing session-wide `i64`
  request sequence across document replacement and lazy runtime creation.
  Inflight responses are removed only after ID, kind, and normalized URL all
  match, so stale same-URL responses and mismatched responses cannot consume a
  current request or mutate cookies/HSTS. Focused regressions prove the stale
  response is rejected, the current fetch remains commit-able, and URL mismatch
  retry succeeds without adding a counter, registry, or request-path scan.
- Stylesheet loading now applies the architecture's shared 1 MiB source
  envelope cumulatively to both raw CSS and retained expanded style HTML across
  inline, override, network, and `@import` paths. Overflow preserves the
  admitted prefix, warns once, and stops the remaining CSS lane before more
  parsing/import work. Retained style chunks join once at finalization instead
  of copying the cumulative string for every sheet. A boundary regression and
  a real `#2563eb` rendered-pixel assertion cover the budget and normal CSS.
  The optimizer/perf runner remains unexecuted because the admitted pure-Simple
  CLI crash and three-cycle build cap are unchanged; no bootstrap/seed fallback
  was used.
- Repeated JavaScript body replacement previously retained one list plus two
  host objects per non-body element forever in the append-only JS object store,
  making memory and reverse property scans grow without a ceiling. The shared
  mutation publisher now rejects before allocation after 32,768 retained bridge
  objects or 64 MiB of retained bridge payload per document. Detached-node
  identity remains correct; focused animation coverage now proves an old node
  cannot alias its replacement and exact object/byte boundaries preserve the
  last admitted rendered DOM. Before: `1 + 2 * descendants` objects per
  replacement without a bound. After: the same browser-correct fresh identities
  up to the fixed cumulative ceiling, then zero additional allocations.
- The optimizer/perf runner and executable rendering spec remain unexecuted
  because the admitted pure-Simple CLI crash and exhausted three-cycle compiler
  cap are unchanged. No bootstrap, Rust seed, or compiler workaround was used.
- Renderer IPC now rejects skipped outer request IDs after endpoint startup,
  closing a stream-poisoning denial where one high ID made every later valid
  frame look duplicate. Input deferred behind an already-sent animation frame
  is re-encoded with the current request ID at activation, so intervening Fetch
  response commands cannot make the worker reject or time out keyboard/pointer
  work. Focused protocol and broker regressions cover consecutive/gapped IDs,
  trailing-message rejection, and the animation -> network -> deferred-input
  sequence. Executable Simple evidence remains compiler-blocked; no bootstrap
  or seed fallback was used.
- Hosted Back, Forward, and Reload commands now validate the BrowserSession-
  owned target before clearing focus or mutating history/runtime state. Page
  focus is discarded without callbacks at the committed navigation boundary,
  with DOM/JS-host focus, selection, and dirty-edit state kept synchronized, so
  blur JavaScript cannot rewrite the validated target or Stop preserve a delayed
  change. Target-bound session operations revalidate immediately before
  traversal. Reload preflight
  reuses the session's normalization and HSTS upgrade policy. The former
  rollback-based worker regression now proves a
  rejected target preserves history, interaction state, scroll, and request
  correlation before a same-ID corrected retry.
- Renderer-originated link and supported form document requests now receive a
  broker-validated one-shot navigation permit only after a parent-owned active
  document origin exists. The boundary accepts exact empty-body GET or
  URL-encoded POST shapes with `include` credentials, rejects added renderer
  headers, preserves any active chrome permit, and routes HSTS through the
  broker redirect path. A focused worker regression drives pointer down/up on
  a submit button, decodes the resulting POST, and proves normal exact permit
  policy accepts it.
- Secondary hosted browser chrome now clears stale address-editing state when
  a non-address control is pressed, so Back/Forward/Home/Reload/Stop/Favorite
  can refresh the visible URL on the next committed frame.
- Authenticated broker HSTS document upgrades now preserve the renderer's
  redirect count as well as the parent permit count; unmarked redirects still
  enforce the normal limit. Focused coverage proves POST body/method/site and
  credential state survive a marked upgrade at the redirect ceiling.
- CSS animations enabled or restarted by JavaScript now use a document-bounded
  per-node epoch instead of inheriting elapsed document time. Epochs are swept
  with computed animation identities, stay outside author markup, affect hit
  testing and pixels identically, preserve paused elapsed time, and extend
  hosted-worker wakeup scheduling.
  Pixel evidence covers an uninterrupted document-start animation beside a
  late-started and restarted class animation.
- Hosted animation scheduling now uses layout's next-change deadline. A
  positive delay sleeps directly to its start boundary instead of triggering
  full parse/style/layout work every 16 ms; focused worker evidence covers a
  one-hour delay.
- CSS attribute selectors now contribute class-level specificity, with a
  canonical Engine2D pixel fixture proving `[data-tone]` beats a later `div`.
- JavaScript timers created after document time advances now schedule from the
  interpreter's current clock; nested callbacks inherit the same drain time.
- Stop clears the canceled address draft so chrome, body, and `current_url`
  consistently show the retained page.
- Same-document pointer/key/text/resize work now uses a bounded 64-command FIFO
  instead of dropping rapid input while the renderer is busy. Navigation,
  network, history, and Stop still reject stale input rather than replaying it
  into a different document.
- Draw IR carries resolved font advances as bounded typed data. Web paint no
  longer builds CSV strings, and Engine2D parses computed-style CSV only for
  legacy external commands.
- Chromium capture and live-window launch no longer disable the OS sandbox.
  Capture disables Node integration, isolates context, and rejects popup or
  staged-page navigation; the live shell explicitly enables renderer sandboxing.
- Broker responses now remove every `Set-Cookie`/`Set-Cookie2` header before
  renderer IPC. The parent jar still stores and attaches both ordinary and
  HttpOnly cookies; a future `document.cookie` read must remain origin-bound
  and broker-mediated rather than restoring response headers.
- Primary hosted renderer startup and successful Favorite toggles now send one
  validated, duplicate-free bookmark snapshot from the parent profile store.
  The protocol caps snapshots at 256 entries and the sandbox worker never reads
  profile files. A busy renderer rejects Favorite before persistence changes,
  so the database cannot diverge from the displayed snapshot.
- Native form reset now restores parsed input, textarea, checkbox/radio, and
  option defaults after one cancelable bubbling `reset` event. Defaults use
  engine-private attributes excluded from author serialization, and explicit
  `form=` ownership shares the normal form-owner resolver.
- Default font caching now keys finite built-in aliases by their resolved font
  path. Custom `@font-face` material remains transient, preventing attacker
  family aliases from pinning duplicate process-lifetime TTF renderers.
- Electron live-smoke validation now parses bounded PNG chunks, validates CRC
  and zlib scanlines, unfilters pixels, and exactly matches checksum, opacity,
  and distinct-color evidence. Compressed and inflated artifacts are capped at
  160 MiB (enough for UHD 8K RGBA); forged dimensions, payloads, or pixel counts
  fail before unbounded read/allocation.
- Remaining production blocker: external `<img src>` resources are not fetched
  or painted. The next lane must route bounded image requests through CSP
  `img-src`, broker HSTS/mixed-content policy, binary image decoding, and the
  canonical layout/Draw IR path; protocol-only admission is not sufficient.
- external-image research: The existing renderer already has the correct
  `DrawIrCommand.image` executor and bounded
  `SimpleOsHostGpuImageResource` codec, but BrowserSession never discovers an
  image, the network/frame protocols reject or omit image material, layout emits
  only a box, and all hosted raster calls pass an empty resource list.
- external-image interfaces: Reuse `SimpleOsHostGpuImageResource` rather than
  adding a second image type. `BrowserSession.image_resources` owns decoded
  document resources; additive layout `*_with_images` entrypoints emit canonical
  image commands; additive `SBRF5` carries a checksummed byte-safe resource
  section while SBRF2-4 remain compatible.
- external-image bounds: The first admitted frame carries at most 64 resources,
  131,072 decoded pixels, and 524,288 resource bytes. Network PNG input remains
  within the existing 524,288-byte response envelope. The general PNG decoder
  rejects dimensions above 4096x4096 or 16,777,216 pixels and bounds inflate to
  the exact expected scanline size before allocation growth.
- external-image security: Ordinary cross-origin images use `NoCors`; CSP
  `img-src`, parent-owned HSTS/mixed-content policy, public-network transport,
  redirects, cookies, and cancellation remain on the existing broker path.
  Image response redirects map to `img-src`, HTTPS downgrade remains rejected,
  and only strict `image/png` responses become renderer resources.
- external-image cooperative review: Sidecars own disjoint PNG decoder,
  SBRF5 protocol, BrowserSession/security, Draw IR/layout, and evidence reviews.
  Merge owner and final reviewer are highest-capability Codex. Frozen manual
  steps are `Load an HTTPS document with an HTTP image under includeSubDomains
  HSTS`, `Fetch and decode the upgraded PNG through the broker`, `Render the
  decoded image through Draw IR`, and `Block the same mixed-content image
  without HSTS`; helpers are `_external_png_pixels`,
  `_external_png_bytes`, `_commit_broker_image_response`, and
  `_render_image_resource_draw_ir`. Any incomplete helper fails explicitly;
  no placeholder pass is permitted.
- external-image implementation: BrowserSession now retains authored/resolved
  image identities, applies CSP and broker transport policy, strictly decodes
  bounded PNG responses, and passes resources through additive `SBRF5` to the
  canonical Draw-IR/Engine2D path. Layout preserves the normal box then paints
  object-fit/object-position image content under ancestor clipping.
- external-image doc refactor: Updated the architecture, detail design, system
  test plan, rendering gap guide, intensive GPU plan, and the original image
  resolver bug. The remaining bug is scoped to CSS `background-image: url(...)`;
  external PNG `<img>` is no longer described as wholly blocked.
- external-image adversarial fixes: CSP evaluates the HSTS-upgraded effective
  URL without bypassing `img-src`; bounded PNG decode receives the document's
  remaining pixel budget before inflate/allocation; and session admission uses
  the canonical resource encoder as an exact `SBRF5` payload preflight.
- external-image verification: two adversarial reviews converged to PASS;
  numbered-artifact, rendering-coupling, direct-env/runtime, conflict,
  placeholder, layout, and static source-shape checks are clean. The pure-Simple
  target compiler blocker still prevents executable specs/docgen, so no runtime
  verification PASS or generated-manual refresh is claimed.
- css-background-image lane (2026-07-29): Reuse `BrowserImageSource`,
  `BrowserSession.image_resources`, `SBRF5`, and the canonical Draw-IR image
  executor. Shared interfaces are `_css_background_image_urls`,
  `_queue_background_image_sources`,
  `_html_draw_ir_background_image_command`, and
  `_render_background_image_pixels`. Manual steps are `Load inline and linked
  CSS background images through the broker`, `Apply background size position
  repeat origin and clip`, `Render the background image behind element
  content`, and `Block background images denied by CSP or mixed-content
  policy`. Sidecars own disjoint CSS discovery/security, layout/paint,
  performance, and evidence reviews; merge owner and final reviewer are
  highest-capability Codex. Any temporary helper must `fail(...)`, never pass.
- css-background-image implementation: Inline, linked, and imported CSS use
  declaration-scoped URL discovery/rewrite and the existing image broker;
  import cascade order, CSP, HSTS, mixed content, repeat/position/size,
  origin/clip, paint order, and referenced-resource filtering have exact
  focused checks. Rounded URL backgrounds and dynamically introduced JS URLs
  remain explicit fail-closed follow-ups; existing CSS/JS animation is kept.
- css-background-image performance: `SBRF6` reuses retained image resources
  with mixed full/reference entries and a load-time position-sensitive
  revision. Stable animation frames do not rescan or base64-serialize retained
  pixels; changed resources invalidate to full entries, cache misses reject,
  and close/image-free paths release retained pixels.
- css-background-image verification: Three bounded adversarial review/fix
  cycles closed URL rewrite, import order, rounded clipping, preflight,
  revision collision, mixed-entry, steady-frame scan, and close-failure cleanup
  blockers. Rendering-source-coupling and direct-env/runtime guards pass.
  Runtime specs were not rerun because the prior focused pure-Simple target
  invocation segfaulted (139); no bootstrap or Rust-seed fallback was used.
- post-load hardening cooperative plan (2026-07-29): Four disjoint sidecars
  own dynamic image admission, GC timer queue removal, deferred Stop IPC, and
  IPv6 HTTPS transport-host normalization. Shared interfaces are
  `BrowserRequest.image_resource_key`,
  `_reconcile_dynamic_image_sources`, `_start_image_source`,
  `stop_after_write`, and `_browser_transport_host`; existing timer
  `pending_timers.remove(...)` is reused. Frozen manual steps are
  `Introduce a background image from JavaScript after load`,
  `Fetch the image through the existing broker policy`,
  `Render the image without resetting animation time`,
  `Cancel a late image response after Stop or navigation`,
  `Drain due GC timers without rebuilding the queue`,
  `Deliver Stop after a partial renderer write`, and
  `Connect IPv6 HTTPS with a bare transport host`. Focused helpers must fail
  explicitly; no placeholder passes are permitted. Merge owner, generated
  manual reviewer, and final adversarial reviewer are highest-capability Codex.
- runtime boundary decision: `runtime_need` is denial of Linux
  `get_robust_list` against the same-UID browser broker after hostile page code
  enters the final site-renderer sandbox. `facade_checked`: this is a seccomp
  policy syscall rule owned by `runtime_process.c`, not an app/library
  capability facade. `chosen_path`: `runtime-owned-change`, adding the syscall
  to the existing final deny filter. `rejected_shortcuts`: no worker-local raw
  syscall shim, Yama assumption, fixture bypass, or parallel sandbox. Frozen
  step: `Deny broker robust-list disclosure from the site renderer`.
- post-load hardening implementation: JavaScript and Simple Script DOM/style
  mutations now reconcile bounded background URLs through request-carried
  resource keys and the existing CSP/HSTS/mixed-content/PNG/Draw-IR path.
  Exact focused evidence reaches rendered pixels without resetting animation
  epochs; redirects retain keys, denied URLs do not consume admission slots,
  failed/canceled requests can retry, and loaded resources survive Stop or a
  failed provisional navigation.
- post-load hardening performance/controls/HTTPS: GC browser timer drain and
  clear mutate the bounded queue in place instead of rebuilding it per
  callback. Stop requested during a partial renderer write is delivered after
  that write, with coalesced worker messages drained and stale replies ignored.
  Canonical URL and HTTP Host keep IPv6 brackets while socket/TLS transport gets
  the validated bare literal.
- post-load hardening security/evidence: The final Linux site-renderer seccomp
  filter denies `get_robust_list`, and the host-native sandbox probe passed with
  exact `EPERM`. Three bounded adversarial passes converged to CLEAR after
  fixing canceled and CSP-denied image admission poisoning. Rendering coupling,
  direct-env/runtime working+staged, reverse-apply, conflict, and placeholder
  gates pass; generated-spec layout remains zero. Pure-Simple executable specs
  remain blocked by the recorded target compiler crash, so no runtime PASS or
  bootstrap/seed fallback is claimed.
- secondary-fidelity cooperative plan (2026-07-29): Small disjoint sidecars
  cover rounded CSS image clipping plus zero-opacity subtree suppression,
  secondary-window bookmark/address state, and in-process IPv6 transport-host
  identity. Shared interfaces are `hosted_browser_transport_host`,
  `content_paint_hidden_by_ancestor`, and registry `set_bookmark_snapshot` with
  `bookmark_revision`/`applied_bookmark_revision`; rounded-image interfaces are
  the `background-shape-*`/`background-radius-*-{x,y}` metadata and
  `_engine2d_draw_ir_css_background_inside_clip`. Frozen manual steps are
  `Render a repeated CSS background inside rounded corners`,
  `Hide an entire zero-opacity subtree`,
  `Synchronize Favorite state across secondary windows`,
  `Restore the committed or startup URL when secondary address editing is
  canceled`, and `Connect in-process IPv6 HTTP and HTTPS with a bare transport
  host`. Focused helpers must fail explicitly. Merge owner and final reviewer
  are highest-capability Codex; no full bootstrap is permitted, and the smallest
  sufficient pure-Simple Phase 2/3 path is allowed only if executable evidence
  becomes essential.
- bounded-frame follow-up: The Draw-IR executor owns one aggregate
  `css_background_pixel_work_remaining` budget per frame, capped to framebuffer
  pixels, in addition to the existing per-command check. The worker computes
  document HTML once per frame and reuses it through
  `prepare_css_animation_instances_with_html`; deferred `resize` replaces the
  newest queued resize while preserving discrete input order. Frozen steps are
  `Bound aggregate CSS background pixel work to one framebuffer`,
  `Reuse one document serialization on a mutating animation frame`, and
  `Coalesce a live resize storm to the latest dimensions`.
- secondary-fidelity implementation: Rounded CSS images retain unclipped clip
  bounds plus effective per-axis corner radii and mask in the existing sampling
  pass. The composition threads one framebuffer-sized remaining-work budget
  through direct, delta, and offscreen paths; missing or inadmissible images do
  not consume it. Zero-opacity subtrees skip paint/Draw IR while retaining CSS
  hit testing. Bookmark snapshots converge by host revision across primary,
  existing secondary, and new windows; secondary Escape restores committed or
  startup URL. Both hosted HTTP owners share IPv6 transport normalization,
  resize storms coalesce, and animation reconciliation/layout reuse one HTML
  serialization.
- secondary-fidelity verification: Highest-capability adversarial review is
  CLEAR after separating paint opacity from semantic hit testing.
  Rendering-source coupling, direct-env/runtime working+staged,
  reverse-apply/whitespace, added-conflict, placeholder, and generated-spec
  layout gates pass. Lightweight LSP diagnostics were unavailable; the bounded
  direct pure-Simple check reproduced the recorded compiler crash (exit 139).
  Per user direction, verification stopped without bootstrap or Rust seed.
- next production-gap cooperative plan (2026-07-29): Six bounded sidecars own
  canonical Draw-IR clipping/z-order, CSP source/meta enforcement,
  scripting/event runtime, chrome/profile/process lifecycle, retained render
  work, and sandboxed evidence contracts. Merge owner, generated-manual owner,
  and final reviewer are highest-capability Codex. Shared interfaces are
  `DrawIrCommand.clip_rect`, `_html_draw_ir_node_paint_order`,
  `browser_csp_source_matches_url`,
  `BrowserSession.script_event_listeners`, `browser_script_event_dispatch`,
  persistent `simple_script_executor`, `SimpleScriptExecutor.tick`,
  `browser_renderer_close_pending`, `SimpleWebRenderSession`, and its
  `document_revision`/`style_revision`/`viewport_revision`/
  `composition_revision`. Frozen manual steps are
  `Clip canonical Draw IR to ancestor overflow`,
  `Paint positioned siblings by stable z-index`,
  `Enforce CSP host paths and head meta policies`,
  `Deliver JavaScript and Simple Script listeners on the live DOM`,
  `Reuse parsed layout work across unchanged animation frames`,
  `Keep secondary chrome usable after primary close`,
  `Retry renderer cleanup after a transient close failure`, and
  `Require sandboxed GPU-backed browser event evidence`. Existing production
  fixture/checker helpers remain canonical; any new temporary helper must
  `fail(...)`, never silently pass.
- meta-CSP blocker (2026-07-29): Meta policies cannot be enforced faithfully
  by a whole-document pre-scan because CSP applies only to following content.
  The current loader extracts scripts, stylesheets, and images into separate
  category-ordered collections without source offsets or per-resource policy
  snapshots. Correct support requires an ordered parser action stream, or
  source offsets plus applicable-policy snapshots for every static resource
  and derived import/module/background-image load. Until then, no unused
  extraction helper is retained and header CSP remains fail-closed.
- CSP host-path hardening (2026-07-29): Initial resource admission compares
  canonical paths after removing literal and percent-encoded dot segments,
  clamps traversal at the URL root, and preserves encoded slashes as data.
  Redirect admission ignores source paths per CSP3 while still matching origin.
- optimization baseline: The authoritative performance SSpec remains
  deliberately fail-fast and the deployed pure-Simple runtime crashes during
  `check` (139), so numeric baseline execution is blocked. Source tracing proves
  one full serialization/parse/style/layout/Draw-IR rebuild per frame; the
  retained-session lane must leave exact stage counters and allocation/RSS
  evidence ready for the smallest working pure-Simple Phase 2/3 runtime. No
  bootstrap or Rust-seed evidence is allowed.
- live script-listener blocker (2026-07-29): Retained JavaScript callables are
  viable, but `be_dom_dispatch_event_path` owns inline capture/target/bubble
  ordering before `BrowserSession` can invoke them. A second JS dispatcher
  breaks mixed-handler ordering and propagation and creates an uncapped
  retained-listener scan. Correct support must extend the one canonical DOM
  dispatcher with a bounded, compacting callable registry, shared Event state,
  and document/window targets. Simple Script callbacks remain separately
  blocked because `ScriptRunner.run_script` denies host execution and
  `SimpleScriptExecutor.tick` has IDs but no executable closure registry. No
  partial listener API was retained.
- next convergence tranche (2026-07-29): Six small sidecars run in parallel:
  essential deployed-compiler crash diagnosis; canonical DOM callable-event
  design; exact retained-render invalidation design; ordered meta-CSP/resource
  design; one bounded HTML/CSS fidelity implementation; and one browser
  chrome/network/sandbox adversarial implementation lane. Merge owner,
  generated-manual owner, and final reviewer remain highest-capability Codex.
  Existing shared owners stay authoritative: `be_dom_dispatch_event_path`,
  `BrowserSession`, `BrowserRenderRevisions`, `BrowserRenderSnapshot`,
  `SimpleWebRenderSession`, `BrowserScriptBlock`,
  `BrowserStylesheetSource`, `BrowserImageSource`, and
  `DrawIrComposition`. Sidecars may not create a second DOM, parser, WebIR,
  event dispatcher, render cache, network stack, or browser controller.
  Frozen manual steps are `Deliver JavaScript and Simple Script listeners on
  the live DOM`, `Reuse parsed layout work across unchanged animation frames`,
  `Enforce CSP host paths and head meta policies`,
  `Render HTML and CSS through canonical Draw IR`, `Operate page and browser
  controls`, and `Run the smallest healthy pure-Simple target check`.
  Existing `_check_event_phase_order`, `_check_canonical_draw_ir`,
  `_check_security_denial`, and `_check_budget_row` remain the checker helpers;
  unfinished production rows keep their existing `fail("REQ-WEB-BROWSER-NNN:
  ... not implemented")` placeholders. No full bootstrap or Rust-seed
  fallback is permitted.
- TDD mandate (2026-07-29): Every product fix in this and later tranches starts
  with a modern `use std.spec.*` system scenario under `test/03_system`, tagged
  to its `REQ-WEB-BROWSER-*`/`NFR-WEB-BROWSER-*` rows, using imperative frozen
  `step("...")` text, canonical matchers, and semantic/Draw-IR/state absolute
  oracles before pixels. Unit tests are supporting evidence only. The mirrored
  `doc/06_spec` operator manual and system-test traceability plan change with
  the scenario. When the unhealthy deployed pure-Simple runtime prevents the
  required red run or docgen, record that exact blocker; never invent a RED,
  hand-edit a generated PASS, substitute the Rust seed, or skip the scenario.
- post-sync production tranche (2026-07-29): Five small guided sidecars own
  disjoint root gaps: per-node image admission identity; canonical callable
  JavaScript event entry; exact retained render revisions; real browser chrome
  control evidence; and one HTTPS/cookie/sandbox adversarial gap. The merge
  owner, manual reviewer, and final reviewer are highest-capability Codex.
  Existing owners remain authoritative: `BrowserImageSource` with one
  `render_resource_key`, `DrawIrCommand.image_uri`,
  `be_dom_dispatch_event_path`, `JsRuntime.invoke_callable_with_this`,
  `BrowserRenderRevisions`, `BrowserRenderSnapshot`,
  `SimpleWebRenderSession`, `HostedBrowserRendererRegistry`, and
  `BrowserSession`. No second DOM/parser/WebIR/renderer/cache/network stack,
  listener dispatcher, cookie jar, TLS verifier, or browser controller is
  permitted. Frozen manual steps are `Bind each image command to its admitted
  node identity`, `Deliver JavaScript and Simple Script listeners on the live
  DOM`, `Reuse parsed layout work across unchanged animation frames`,
  `Operate page and browser controls`, and `Navigate through verified HTTPS`.
  Existing `_check_canonical_draw_ir`, `_check_event_phase_order`,
  `_check_budget_row`, `_operate_browser_navigation`, and
  `_check_security_denial` helpers remain canonical. Every implementation
  starts with its modern system SSpec and retains `fail("REQ-WEB-BROWSER-NNN:
  ... not implemented")` for unfinished rows. The deployed CLI exit-139 ABI
  blocker still forbids fabricated runtime PASS, Rust-seed substitution, or
  full bootstrap.
- post-sync tranche implementation (2026-07-29): Image admission now binds one
  opaque render key to the canonical body node through existing NUL-hidden DOM
  metadata; authored DOM/CSS serialization omits it, render serialization
  consumes it, and remove/reorder cannot invert identical-URL CSP decisions.
  Stylesheet occurrences retain their ordered source binding and allowed
  identical URLs share the existing decoded pixel resource. The canonical
  fetch path replaces forged CORS `Origin` headers with the parsed requester
  origin on each hop. Secondary address input now enforces the same 2048-byte
  UTF-8 bound as primary chrome. `display:inline-block` retains its computed
  value and uses one atomic inline-run layout path with Draw-IR and Engine2D
  absolute oracles; baseline alignment remains explicitly unsupported.
- retained/event foundation (2026-07-29): `BrowserRenderRevisions`,
  `BrowserRenderSnapshot`, and one worker-owned `SimpleWebRenderSession` reuse
  unchanged compositions before serialization/parse/style/layout/paint.
  Document, stylesheet, and image binding/pixel mutations invalidate exact
  revisions; worker close delegates to real `BrowserSession.close()` and clears
  timers, runtime, loads, requests, modules, images, bindings, DOM/style/source,
  history, overrides, hit state, and retained counters. No timing/RSS/NFR-003
  claim is attached to the functional reuse counter scenario. The existing JS
  interpreter exposes direct host callable invocation and the one canonical DOM
  dispatcher accepts a private executor cursor with bounded listener tombstone
  reuse. BrowserSession callable-listener integration and JS-originated
  synchronous `dispatchEvent()` remain RED because active-interpreter re-entry
  is not implemented.
- post-sync tranche verification (2026-07-29): Two adversarial review/fix
  cycles converged to PASS after closing async resource/style invalidation,
  real lifecycle reclamation, DOM-reorder CSP identity, duplicate dispatcher
  API, boolean matcher, Engine2D oracle, and conformance-ledger blockers.
  Conformance contract, rendering-source coupling, direct-env/runtime
  working+staged, reverse-patch whitespace, conflict/placeholder scan, SPipe
  wiring, and generated-spec layout (`0`) pass. Executable SSpec/docgen/live
  animation evidence remains blocked by the recorded deployed pure-Simple
  exit-139 ABI artifact; no bootstrap or Rust seed was used.
- live-interaction tranche (2026-07-29): Six small guided sidecars own
  disjoint next gaps: BrowserSession callable JavaScript listeners; persistent
  SimpleScript timer/animation callbacks; retained selective invalidation;
  production chrome navigation evidence; cookie/security enforcement; and one
  bounded table-formatting HTML/CSS slice. Existing owners remain canonical:
  `JsRuntime.invoke_callable_with_this`, `be_dom_dispatch_event_to_id`,
  `BrowserSession`, `SimpleScriptExecutor`, `BrowserRenderRevisions`,
  `SimpleWebRenderSession`, `HostedBrowserRendererRegistry`, `CookieStore`,
  and the shared HTML style/layout pipeline. No second interpreter, DOM/event
  dispatcher, timer queue, render cache, controller, cookie jar, parser, WebIR,
  or renderer is permitted. Frozen steps are `Deliver JavaScript and Simple
  Script listeners on the live DOM`, `Run JavaScript and advance the browser
  clock`, `Reuse parsed layout work across unchanged animation frames`,
  `Operate browser navigation controls`, `Exercise host-only Secure HttpOnly
  SameSite path and expiry`, and `Render HTML tables through canonical Draw
  IR`. Existing `_check_event_phase_order`, `_advance_browser_clock`,
  `_check_budget_row`, `_operate_browser_navigation`, and
  `_check_security_denial` helpers remain canonical. Each product edit begins
  with a modern system RED and mirrored manual; unfinished rows keep their
  explicit `fail(...)`. No full bootstrap or Rust-seed fallback is permitted.
- live-interaction implementation (2026-07-29): The canonical BrowserSession
  dispatcher now delivers retained JavaScript listeners with target fields,
  cancellation, mutation-during-dispatch, and reset semantics; synchronous
  JavaScript-origin re-entry remains an explicit fail-closed RED. The existing
  SimpleScript executor retains bounded timer, interval, and animation-frame
  callbacks, and load-time style commands join the canonical final stylesheet
  exactly once. `SimpleWebRenderSession` retains parsed/style/layout material,
  invalidates by exact revision, and computes Draw-IR evidence hashes lazily.
  Hosted chrome/page input ownership rejects stale same-window, cross-window,
  and page/chrome releases. The existing cookie store carries Secure,
  HttpOnly, SameSite, expiry, and schemeful-site partition keys through real
  BrowserSession redirect hops. The canonical table owner now collects direct
  and grouped rows for fixed layout, captions, and bounded colspan lowering.
- live-interaction verification (2026-07-29): Modern SSpec/manual evidence
  covers listener fields and mutation ordering, timer/rAF styling and pixels,
  retained invalidation/reuse and lifecycle plateau, chrome navigation/input
  replacement, cookie admission/isolation/deletion and observed redirect
  requests, and table semantic/Draw-IR geometry before Engine2D pixels. Two
  independent adversarial reviews converged after repairing eager Draw-IR
  hashing, stale input clearing, direct-only table traversal, incomplete cookie
  partition plumbing, and overwritten load-time SimpleScript style. Runtime,
  executable SSpec, docgen, and live animation execution remain blocked by the
  recorded deployed pure-Simple exit-139 ABI artifact; no bootstrap or Rust
  seed was used.
- remaining-production audit tranche (2026-07-29): Three small read-only
  sidecars rank the next executable gaps: HTTPS/sandbox/capability evidence,
  the remaining bounded WPT CSS ledger, and native lifecycle/performance
  evidence. Canonical owners are frozen before fan-out. Security stays in
  `HostedBrowserRendererProcess`, its existing platform sandbox policy,
  `BrowserSession`, `FetchEngine`, the canonical TLS/origin services, and the
  parent broker; CSS stays in the existing HTML style/layout producer and
  `DrawIrComposition`; lifecycle stays in `SimpleWebRenderSession`,
  `BrowserSession.close()`, and the hosted renderer registry. No second TLS
  stack, sandbox, browser controller, DOM, parser, WebIR, Draw IR, renderer,
  compositor, cache, profiler, or GC owner is permitted. Frozen manual steps
  are `Navigate through verified HTTPS`, `Reject renderer host capability
  access`, `Bind platform sandbox evidence to the production renderer binary`,
  `Render HTML and CSS through canonical Draw IR`,
  `Reuse parsed layout work across unchanged animation frames`, and
  `Close the page and reclaim browser resources`. Existing
  `_check_security_denial`, `_check_canonical_draw_ir`, `_check_budget_row`,
  and `_check_resource_reclaimed` helpers remain authoritative; unfinished
  product rows retain explicit `fail(...)`. The merge owner and generated
  manual reviewer are root Codex, followed by an independent high-capability
  read-only review. No runtime execution or bootstrap is authorized during the
  audit.
- remaining-production audit result (2026-07-29): The next TDD tranche fixes
  three independently confirmed root defects. First, the hosted broker removes
  its caller-supplied `authenticated_https` decision and permits HSTS learning
  only on the existing completed platform-HTTPS job path; mocks, plaintext,
  invalid/failed TLS, and ordinary response finalization cannot learn policy.
  Second, `SimpleScriptExecutor.reset()` releases the old `ScriptRunner` DOM,
  event loop, and bounded console material so navigation/close cannot retain
  the prior document through the persistent executor. Third, the canonical
  inline-run formatter aligns empty atomic inline-blocks by their bottom margin
  edge and offsets the complete existing layout subtree before Draw IR.
  Security evidence also records that the current hosted-WM wrapper injects an
  unhashed bootstrap runtime DSO and therefore remains blocked rather than
  qualifying as production proof; repairing that evidence wrapper is a later
  owner lane, not a browser-core shortcut. Current primary sources are RFC
  6797, RFC 9525, CSS 2 inline-block baseline rules, and CSS Inline Layout
  baseline alignment. The three implementation sidecars use the already frozen
  owners and manual steps, write modern SSpec RED oracles before product edits,
  and do not run the unavailable runtime or any bootstrap.
- remaining-production implementation and review (2026-07-29): The broker no
  longer accepts caller-supplied HTTPS authentication and learns HSTS only
  inside the successful platform HTTPS job completion. SimpleScript reset
  releases old DOM/event-loop/console/callback-source ownership on navigation
  and close. The canonical inline formatter aligns the supported empty atomic
  inline-block slice using signed parent-strut leading, resolved positive pixel
  margin edges, and complete-subtree offsets before Draw IR. Modern SSpec and
  mirrored manuals assert generic HSTS denial, preloaded persistence,
  callback-body/queue/console reclamation, computed style, line geometry, and
  Draw IR. Two adversarial reviewers rejected early false-green HSTS persistence
  and baseline math; after two repair cycles both returned PASS. Live trusted
  and invalid-certificate HTTPS, negative/percentage and non-empty/overflow
  baseline cases, native performance/RSS/GC, Windows/macOS sandbox rows, and
  the unadmitted hosted-WM runtime DSO remain explicit blockers. Documentation
  refactor updated architecture, design, plans, manuals, domain research, the
  open bug record, and this state; no workflow/command surface changed, so
  `.codex`/`.agents`/`.claude`/`.gemini` instruction updates are N/A.
- deployed-runtime revalidation (2026-07-29): The current deployed artifact at
  `/home/ormastes/dev/pub/simple/bin/release/x86_64-unknown-linux-gnu/simple`
  has SHA-256
  `40edbb4989132623fc57d770b7c02fa85760ec0dd02405d5c22e568e0063e41b`
  and exits zero for `--version`, but prints the explicit Rust bootstrap-seed
  warning. It is not the required pure-Simple self-hosted CLI and cannot run
  SSpec, docgen, browser, performance, or release evidence. The prior exit-139
  artifact identity is superseded, but the production-runtime gate remains
  blocked for a different, directly observed reason. No target spec was run
  and no bootstrap was started.
- next-gap audit tranche (2026-07-29): Three small read-only sidecars rank the
  existing hosted-WM runtime-provider admission flaw, page Node/native/scheme
  capability exposure, and WPT multiple-background layers. Canonical owners
  remain `check-linux-hosted-wm-live-window-evidence.shs`,
  `HostedBrowserRendererProcess` plus the existing browser-only JavaScript and
  scheme policy, and the existing HTML CSS/declaration/layout/Draw-IR pipeline.
  Frozen steps are `Bind platform sandbox evidence to the production renderer
  binary`, `Reject renderer host capability access`, and `Render HTML and CSS
  through canonical Draw IR`; existing `_check_security_denial` and
  `_check_canonical_draw_ir` helpers remain authoritative. No new runtime
  loader, TLS/sandbox/controller, JS profile, parser, WebIR, Draw IR, renderer,
  or compositor is permitted. Audit sidecars do not edit or run runtime,
  bootstrap, seed, or network commands.
- next-gap selected lane (2026-07-29): The hosted-WM evidence wrapper is a
  confirmed false-green owner: it defaults to a bootstrap runtime DSO, admits
  it by size alone, and appends ambient `LD_PRELOAD`. The bounded TDD repair
  stays in `check-linux-hosted-wm-live-window-evidence.shs` and its existing
  shell/static tests: require an explicit non-bootstrap runtime provider and
  expected SHA-256, recheck identity before launch, sanitize loader injection,
  and emit the admitted provider identity in the receipt. It does not build or
  alter a runtime, compiler, browser sandbox, loader, or rendering owner.
- next-gap CSS lane (2026-07-29): Multiple CSS background images are blocked
  before Draw IR because the shared stylesheet URL scanner admits only one
  URL and paint lowering rejects `bg_layers_raw`. The bounded TDD slice reuses
  the existing Style, BrowserImageSource admission, Draw IR CSS-background
  commands, and Engine2D sampler for exactly two URL layers with existing
  scalar longhands. It emits the CSS back layer before the front layer and
  keeps gradients, mixed image types, local attachment, and more than two
  layers explicitly unsupported. No new parser, WebIR, Draw IR kind, renderer,
  compositor, framebuffer, or resource owner is allowed.
- capability audit result (2026-07-29): BrowserSession uses the existing
  browser-only JavaScript runtime, so Node globals are not the observed gap.
  A separate hosted-WM path evaluates bridge-owned non-browser HTML in an
  in-process `HostedWebContentSession`; positive `HostedWindow.owner_port`
  already identifies that remote provenance. Existing integration tests,
  however, intentionally define interactive remote host HTML as supported.
  Routing positive-owner content to the existing external browser renderer or
  inert output therefore needs an explicit contract migration and is not
  silently changed in this tranche. REQ-WEB-BROWSER-014 remains RED for this
  boundary mismatch; no sandbox or host-script false-green is claimed.
- Draw IR refactor lane (2026-07-29): The shared visible-material witness
  appends immutable text once per visible command in both Draw-IR and software
  render paths, causing quadratic copied bytes and transient text allocation.
  The bounded TDD refactor stays in
  `_simple_web_visible_material_witness`: collect the existing ordered CPU and
  solid witness lines, then join each list once. Witness ordering/hash,
  animation provenance, `DrawIrComposition`, and Engine2D behavior remain
  unchanged; no WebIR type or parallel rendering path is introduced.
- next-gap implementation/review (2026-07-29): The bounded two-URL
  `background-image` profile now admits both resources through the existing
  BrowserSession policy, lowers the back then front layer through typed Draw
  IR, blends through Engine2D, rejects shorthand/malformed/missing/denied
  pairs atomically, and retains the remaining CSS ledger exclusions. The
  visible-material witness now joins ordered visible CPU/solid lines once
  instead of repeatedly copying growing text. Root review repaired a partial
  layer leak and border-overlay regression; independent cycle-2 review
  returned PASS for CSS, Draw IR ordering, CSP/missing-resource denial,
  allocation guarding, witness identity, and animation preservation.
- runtime-provider review limit (2026-07-29): Wrapper hardening now requires
  explicit hash admission, rejects canonical/current copied bootstrap content,
  stages privately, binds the launched DSO through inherited fd 9, sanitizes
  loader variables, cleans its stage, and validates nonempty lower-hex receipt
  values. After three review/fix cycles one blocker remains: when the canonical
  bootstrap DSO is absent, no trusted build provenance or pinned forbidden
  content identity distinguishes an arbitrarily copied bootstrap DSO from a
  production provider. The wrapper improvements remain useful fail-closed
  hardening, but this tranche does not promote hosted-WM evidence to production
  PASS or close the existing runtime-provider bug.
- production-gap audit tranche (2026-07-29): Six guided read-only sidecars
  selected disjoint root defects under existing owners. Cookie replacement
  must include `partition_key`; positive-owner hosted HTML must use the
  existing external renderer registry while owner-zero local content retains
  its current lane; focus transitions must blur the old target and apply the
  new focus state before the new focus listener. Explicit-width
  `table-layout:auto` may add one O(cells) non-spanning column-minimum pass.
  One bounded fractional-opacity subtree may partition canonical absolute
  Draw-IR commands into pre/group/post batches and reuse existing
  `embedding.opacity_milli` group compositing. Per-frame image resource
  selection/coverage may replace nested URI scans with transient ordered
  indexes. Frozen manual steps remain `Reject renderer host capability access`,
  `Render HTML and CSS through canonical Draw IR`, `Reuse parsed layout work
  across unchanged animation frames`, and `Close the page and reclaim browser
  resources`; cookie coverage reuses `Keep partitioned and unpartitioned names
  distinct`. No new DOM, clock, dispatcher, table engine, WebIR, Draw-IR kind,
  renderer, compositor, framebuffer, resource owner, or retained cache is
  permitted. Residual table spans/collapsed borders, multiple/nested opacity
  groups, remote URL content-kind loss, live TLS, native performance, and
  runtime-provider provenance remain explicit RED rows. Root Codex is merge
  and generated-manual owner; implementation sidecars write real RED oracles
  first and an independent high-capability reviewer accepts the merged result.
  The deployed CLI was rechecked at the same SHA-256
  `40edbb4989132623fc57d770b7c02fa85760ec0dd02405d5c22e568e0063e41b`
  and still identifies itself as the Rust bootstrap seed, so no target spec,
  docgen, runtime, bootstrap, or network command is authorized in this tranche.
- HTML/CSS conformance expansion (2026-07-29): Repository inventory confirmed
  there is no trustworthy standards-Markdown-to-SSpec generator. The canonical
  path is manual-first executable SSpec under `test/` followed by pure-Simple
  `spipe-docgen`; the legacy extractor emits placeholder-prone tests and is not
  admitted. “WebIR” remains the existing HTML semantic/style/layout model, not
  a new IR type. Every newly admitted case must witness that model, the same
  downstream `DrawIrComposition`, and Engine2D output. Legacy HTML visible-text
  suites are being relabeled without widening their claims; generated manuals
  remain pending a qualified pure-Simple runtime. The open `std.spec`
  last-expect masking root is repaired by identity-preserving accumulated
  failures plus child-runner adversaries, including hook failure and
  `expect(false).to_equal(false)` isolation. A sidecar nevertheless invoked
  the unqualified deployed artifact once during object-fit checking; its ABI
  probe failed and the direct artifact segfaulted. No result was accepted, no
  bootstrap/Rust fallback followed, and that command must not be repeated.
  Broad transform changes were reverted after review found normal-flow
  corruption. Rejected supports/custom-property/specificity work is retried
  only in `/tmp/simple-css-d1-retry.20260729` for reviewed patch import.
- browser boundary and interaction tranche (2026-07-29): Hosted and worker
  address editing now keeps `about:blank` until commit, restores the committed
  URL on Escape, and enforces the 2048-byte UTF-8 limit atomically. Missing or
  invalid button types use the shared submit default while explicit
  `type=button` remains inert. CSP sandbox capabilities intersect repeated
  header policies, gate inline handlers/forms/top navigation/storage/cookies,
  and use an opaque `null` initiator without ambient cookie authority.
  The hosted broker now validates every untrusted SBRQ4 initiator before
  cookie writes or fetch: only its trusted requester or `null` is admitted,
  and `null` requires `credentials=omit` with no script cookie writes.
  Cookie storage limits the serialized UTF-8 `name=value` pair to 4096 bytes,
  preserves global creation ordering across jars and replacement, and keeps
  the bounded raw setter transport distinct at 8192 bytes. Independent
  security and interaction reviews returned PASS after the final adversarial
  protocol-boundary repair.
- retained animation and manual evidence tranche (2026-07-29): Hosted animation
  invalidation reuses retained CSS animation instances and reconciles dynamic
  class changes once. Duration, delay, and iteration schedules are retained as
  typed fields, so the hot next-frame helper performs arithmetic only and no
  longer splits or reparses text each tick; delayed, paused/resumed, infinite,
  finite-end, title-only rAF, and quiescent behavior remain covered. The
  phase-2/3 pure-Simple docgen artifact regenerated 47 affected browser,
  HTML, CSS, security, runner, and docgen manuals with
  `47 complete, 0 stubs`; no full
  bootstrap or target-runtime claim was made. Previously step-less changed
  specs now expose immediate imperative `step("...")` flows. Native browser,
  live HTTPS/certificate, platform sandbox, RSS/GC/soak, and production
  performance evidence remain active blockers rather than PASS claims.
- rendering/event-loop tranche (2026-07-29): Successful address submission now
  releases chrome focus while rejected navigation preserves editing. Paint-only
  animation properties reuse layout boxes and repaint canonical Draw IR;
  layout-affecting or unknown properties still relayout. Browser HTML retains
  one canonical parsed document instead of serializing and reparsing the visible
  body. Sticky positioning is conservatively limited to root/html/body ancestry,
  preserves auto inset sentinels, and rejects transformed or nested-scroll
  cases; exact Draw IR and Engine2D pixel oracles cover both supported and
  fallback behavior. Canonical JS timers now select nextTick/FIFO or earliest
  stable deadline in one scan, remove completed entries with swap-pop, and
  checkpoint microtasks under the shared 1000-job yield budget. Independent
  reviews returned PASS. Four affected manuals were regenerated with the
  phase-2/3 pure-Simple docgen (`4 complete, 0 stubs`); no bootstrap or target
  runtime claim was made.
- renderer site-isolation tranche (2026-07-29): Each hosted child generation is
  locked to one immutable schemeful site. Direct cross-site navigation requests
  signal a swap before network start; cross-site redirects withhold response
  metadata and body before child IPC. The registry closes the old process,
  installs a fresh monotonic generation and decoder, carries only broker-owned
  cookies plus validated navigation metadata, HSTS, home, history, and
  bookmarks, and rejects stale SBRQ4 traffic. Independent high-risk review
  returned PASS. The two affected manuals were regenerated (`2 complete,
  0 stubs`); live target-runtime isolation remains an evidence blocker.
- retained pointer and HTTPS deadline tranche (2026-07-29): Non-external hosted
  Web pointer edges now reuse one owned `SimpleWebRenderSession` and its
  canonical retained hit index instead of reparsing HTML/CSS and relaying out
  on press and release. Mutations invalidate retained state and both close paths
  release it; counter and animated-geometry oracles passed independent review.
  Rustls browser HTTP jobs now apply the absolute job deadline to every TLS
  read, write, and flush, preventing silent peers from pinning the 64-job pool;
  the deterministic silent-peer unit checks timeout classification, empty
  response, retirement, and Unix/Windows timeout variants. Independent review
  returned PASS. The affected SSpec manual was regenerated (`1 complete,
  0 stubs`); no bootstrap or target runtime was run.
- HTML named-reference tranche (2026-07-29): The canonical tokenizer now uses a
  generated pure-Simple 2,231-entry WHATWG-compatible named-character table and
  bounded 32-byte longest-prefix lookup, including 93 two-scalar expansions and
  attribute-context legacy suppression. Numeric and unknown-reference behavior
  remains on the canonical tokenizer path. A deterministic repo-style `.shs`
  generator pins CPython 3.12.3 source data, cardinalities, and digest; PSF-2.0
  attribution and license treatment are bundled. Independent review returned
  PASS and the affected SSpec manual regenerated (`1 complete, 0 stubs`).
- navigation supersession tranche (2026-07-29): Hosted renderer Navigate,
  Home, Back, Forward, and Reload now validate permits and encode sanitized
  replacement commands before canceling a fully-sent slow navigation. Partial
  IPC frames still fail busy without corrupting framing; valid replacements
  reuse canonical stop cleanup to free network/deferred/animation/provisional
  state. Encoded stale SBRQ4 fetch and SBRF5 frame replies are rejected by the
  production poll classifier without mutating the replacement document,
  history, provisional state, or permit. Independent review returned PASS and
  the affected manual regenerated (`1 complete, 0 stubs`).
- keyboard event tranche (2026-07-29): Hosted and worker K2 input now route raw
  keys through one typed BrowserSession/BeDOM event path. JavaScript and Simple
  Script observe canonical `key`, `code`, Shift/Control/Alt/Meta, and repeat
  values; shifted digits, punctuation, navigation/editing keys, Insert/Delete,
  F1-F12, modifiers, and unknown keys have explicit mappings. Shift+Tab
  cancellation preserves focus and dispatch remains stateless. Independent
  review returned PASS after import and mapping repairs. Three affected manuals
  regenerated (`3 complete, 0 stubs`); K2 wire format remains unchanged.
- canceled text-edit tranche (2026-07-29): Canonical BrowserSession selection
  now collapses after Backspace/Delete only when the successful
  `beforeinput` dispatch was not canceled. Hosted and worker K2 rows preserve
  the UTF-8 `1..3` selection over `é`, emit `beforeinput` without `input` or
  `change`, reuse the retained focus for Shift+ArrowRight, and clear selection
  state on blur. Independent review returned PASS. The new modern SSpec manual
  regenerated with 108 authored lines (`1 complete, 0 stubs`, no warnings).
- image-resource validation tranche (2026-07-29): BrowserSession image admission
  now calls a shared nonallocating validator instead of encoding, checksumming,
  and discarding the full retained image wire payload. The encoder reuses the
  same validation ordering and materializes URI/pixel bytes only for emission;
  UTF-8 URI length uses the O(1) byte-length path with overflow-safe totals.
  Validator/encoder rejection parity, a multibyte near-limit URI, 256 same-key
  replacements, revision bounds, navigation cleanup, and close cleanup passed
  independent review. Two manuals regenerated (`2 complete, 0 stubs`).
- open JS VM retention blocker (2026-07-29): Read-only ownership tracing proved
  each listener call appends an Event object/methods/global plus an invocation
  environment and `arguments` object. No deletion, sweep, compaction, or
  free-list API exists, and stored invocation frames make Event-only escape
  detection unsafe. The concrete root fix and 1,000-dispatch/escaped-identity
  evidence are recorded in
  `doc/09_report/js_event_dispatch_vm_growth_2026-07-29.md`; no unsafe
  Event-only reuse was accepted. A reviewed lexical-parent prerequisite remains
  uncommitted at `/tmp/simple-js-lexical-parent-worktree.P06ifr`: its unit
  compile passes, but cycle-3 docgen evidence incorrectly reports an
  unconditional pending reclamation scenario as active and emits code fragments
  as operator steps. The full 1,000-dispatch reclamation bound remains RED.
- broker CSP enforcement tranche (2026-07-29): The hosted broker now owns and
  intersects header/meta CSP, restores committed/pending/history policy through
  production site swaps, rejects missing/invalid or base-policy-failed requests
  before navigation, cookie mutation, or transport, rejects opaque-sandbox
  cookie writes, and keeps top-level document downgrade outside the subresource
  mixed-content shortcut. Adversarial decoded SBRQ4 evidence traverses the
  production dispatch path. Independent security and generated-manual reviews
  passed; commit `5aaa58f02936` is on GitHub.
- CSS table spacing tranche (2026-07-29): `border-spacing` is parsed, inherited,
  carried through Web layout/Draw IR, and applied to fixed and constraint-aware
  automatic tables. Vertical-only `0 3px`, min-width, colspan, row-group,
  caption, CSS-wide, invalid-negative, oversized containment, and zero-spacing
  controls passed independent review. Commit `a4e587120b47` is on GitHub.
- phase-2 docgen runtime repair (2026-07-29): Native `rt_to_string` no longer
  dereferences boxed integer `2026 << 3` as an array; aggregate dispatch first
  proves registry membership. The C selfcheck passes, the phase-2 docgen built
  `69 compiled, 0 failed`, and CSP/JS manuals regenerated with zero stubs. The
  exact evidence and binary hash are in
  `doc/08_tracking/bug/native_rt_to_string_boxed_i64_array_probe_sigsegv_2026-07-29.md`;
  commit `03064ec97087` is on GitHub. No full bootstrap or Rust-seed fallback
  was used.
- parser artifact divergence (2026-07-29): Current pure-Simple parser source
  successfully parses bare, field, compound, and walrus assignment RHS
  continuations through a focused compiled parser probe. Deployed Stage2
  (`58c2827c…`) and retained old Stage3 (`98087781…`) still reject the same
  source before target closure discovery. One current-source Stage3 production
  attempt emitted no progress for three minutes and was terminated; no full
  bootstrap or seed fallback was used. JS reclamation and BrowserSession
  animation execution remain blocked until a fresh pure-Simple compiler
  artifact is admitted.
- hosted input receipt tranche (2026-07-29): The production hosted key path
  now snapshots its semantic target before Enter/Escape clears address-edit
  state, so evidence retains `browser:parent#address` instead of falsely
  recording `browser:page`. The shared semantic receipt contract now accepts,
  stores, and serializes the input timestamp already supplied by every hosted
  caller, repairing the seven/eight-argument type-check break. Focused Stage2
  native compilation completed with zero failed files; the produced probe hit
  the existing unhealthy native-runtime segfault, so no live interaction PASS
  is claimed.
- local TLS ABI gate restoration (2026-07-30): Missing fixtures made negative
  cases vacuous and obscured the whole-gate failure behind trusted-path errors.
  Restored fixtures plus file and key-pair preflight now fail closed; trusted,
  mismatch, untrusted, stall, reset, and trickle modes pass. This proves only
  `rt_tls_client_*` address+SNI behavior, not hosted `rt_browser_http_job`, a
  live `BrowserSession`, or a TLS production row.
- runtime sandbox receipt (2026-07-30):
  `sh test/01_unit/runtime/run_process_piped_write_test.shs` now emits
  `STATUS: PASS browser renderer runtime sandbox` only after its live C gate.
  The narrow claim is current runtime `rt_browser_renderer_spawn_sandboxed`
  preinit plus `rt_browser_renderer_sandbox_enter` second-stage path:
  environment/cwd/inherited-FD sanitization and Landlock/seccomp/rlimit
  containment/limits. It does not admit a hosted renderer artifact, prove
  broker/CSP or Electron containment, or promote a SANDBOX production row.
- held browser bundle (2026-07-30): Four isolated patches remain unmerged.
  DrawIR canonical oracle (`/tmp/simple-drawir-canonical-oracle.VBRqIv`),
  content-visibility GPU guard (`/tmp/simple-content-visibility-gpu-guard-20260730`),
  and address bound (`/tmp/simple-address-bound.Qw0wSt/worktree`) each have
  static, phase-2 manual, and high-capability review PASS, but no executable
  proof. EventLoop idle drain (`/tmp/simple-eventloop-idle-drain`) is HOLD/FAIL:
  its future-timer case is vacuous, it has no performance discriminator, and
  its tick wording is stale; review/docgen reached the cycle cap. Resume only
  with an admitted current pure-Simple full CLI, running each focused spec once;
  no seed or bootstrap substitute. Root Codex is merge owner and final reviewer.
- JS VM animation-retention blocker (2026-07-30): Repeated rAF
  `body.innerHTML` replacement allocates seven bridge objects per frame and
  drives fresh-generation property scans to Theta(frames^2); frame 4,682 is
  rejected by the cumulative 32,768-object cap. Bridge-only deletion is unsafe
  because detached elements, callbacks, listeners, and closures can escape.
  The scoped tracing-GC diagnosis/design passed high-capability review, but its
  SSpec, N/2N performance gate, implementation, and production receipt remain
  RED/open. Detail:
  `doc/08_tracking/bug/js_vm_dom_bridge_retention_quadratic_2026-07-30.md`.
- intensive HTML/CSS and animation held tranche (2026-07-30):
  CSP-clock (`/tmp/simple-animation-csp-clock`) has production, spec, phase-2
  manual, and high-review PASS. Table collapse
  (`/tmp/simple-table-collapse-slice`) has cycle-2 production, spec, manual,
  and high-review PASS. Both remain unexecuted and unmerged. Object-fit
  inheritance (`/tmp/simple-object-fit-inheritance.w2dMXw`) has production and
  spec high-review PASS, but its generated manual failed because it exposes a
  fifth cleanup action; the three-cycle cap is exhausted. rAF frame alignment
  (`/tmp/simple-raf-frame-align-clean.gdkM4F`) has production, spec, phase-2
  manual, and final high-review PASS, but remains unexecuted and held for an
  admitted current pure-Simple full CLI. The animation
  layout-classification cache
  (`/tmp/simple-animation-layout-cache.Fh8uZo`) has production and spec
  high-review PASS, but its phase-2 manual failed on a raw inline-CSS payload
  bullet at the regeneration cap.
  Fractional-opacity group compositing has a high-review-PASS
  architecture/design/system-test proposal but remains unimplemented. No
  target behavior or executable PASS is claimed: an admitted current
  pure-Simple full CLI remains unavailable, and each applicable focused SSpec
  must run once after admission. No bootstrap or seed substitute is authorized.
- intensive batch-2 ledger (2026-07-30): Details/summary rendering
  (`/tmp/simple-details-summary-render`) has an O(N) production pass, modern
  four-step SSpec, phase-2 manual, and high-review PASS, but remains held and
  unexecuted. Invalid form method
  (`/tmp/simple-invalid-form-method.M1cWuX`) has production, modern SSpec,
  canonical phase-2 manual, and final high-review PASS, but remains held and
  unexecuted. The maxlength candidate was rejected because leading-digit
  parsing is the required non-negative-integer behavior, not a bug.
  `overflow: clip` remains RED after its patch was rejected for losing
  origin/`@layer` provenance; implementation requires parser -> `Rules` ->
  cascade-owner provenance. History API remains a structural RED until a
  bounded full-ledger/current-index protocol and parent-issued CSP witness
  replace neighbor-only validation. Primary-renderer close retry
  (`/tmp/simple-primary-close-retry.RotRUO`) is HOLD/FAIL at the three-review
  cap: fatal poll revokes authority inside an already-entered block, but
  `begin_resize` lacks a fresh authority check and may call the closed/failed
  renderer. Other lifecycle work reviewed sound; none of it is promoted or
  merged. Fractional animation (`/tmp/simple-animation-slice2`) is HOLD/FAIL at
  the three-review cap: invalid longhand/shorthand tails erase the earlier
  valid winner (`2; -1` computes default 1 and an invalid shorthand wipes its
  predecessor), while reconcile (`current - old.start`, `current -
  old.paused`) and apply (`animation_time - start`) retain unchecked i64
  subtraction. A fresh cycle must implement last-valid selection and saturating
  subtraction with i64-min/boundary evidence. The f64, negative-zero,
  fractional, zero, infinite, fill, exact-color, and checked-add work reviewed
  sound but remains unpromoted. No patch is merged, no target SSpec has
  executed, and no acceptance row is promoted by this ledger.
- bookmark title witness design (2026-07-30): Read-only origin/main tracing
  proved that both sandbox hosted Favorite paths persist
  `toggle_bookmark(url, url)`, while the in-process profile reconciliation also
  overwrites `BrowserSession.current_title` with `(url, url)`. The resulting
  persisted and UI-access bookmark label is the URL after profile/renderer
  restart. Architecture, detail, system-test, and agent-plan contracts now
  propose additive `SBRF8` title evidence bound to generation/reply/committed
  URL, a shared 512-byte UTF-8 title validator with derived URL fallback, and
  one exact four-step 512/513-byte persistence/listing SSpec. This is
  PROPOSED/UNIMPLEMENTED: no source/spec/manual/build/commit/push or acceptance
  promotion exists.
  Cycle-1 design repair adds pre-decode `title-len <= 684`, canonical base64
  round-trip, checked payload offsets, and encoded-plus-decoded title charging
  against the existing 1 MiB frame/Draw-IR budget before allocation. The same
  four visible steps now require a public-action-only
  `HostedWebContentRegistry` Favorite -> file-backed profile -> reopened
  registry assertion, with no direct BrowserSession access, so in-process
  `(url, url)` removal must match sandbox behavior.
- rejected design bundles (2026-07-30): The hosted HTTPS plan is HOLD/FAIL at
  the three-review cap because HSTS belongs to the broker, not the worker, and
  renderer launch must unset `LD_LIBRARY_PATH`. The parent-history plan is
  HOLD/FAIL at the same cap because `SBRHJ1` lacks one canonical
  omitted/null/empty URL representation and an exact fragment-preserving
  empty-string oracle. All other reviewed aspects are sound but unpromoted;
  neither failed plan is imported, and the history design slot remains pending.
- SimpleScript listener bundle (2026-07-30): Production, a modern SSpec, its
  phase-2 manual (`complete 1/1`, `stubs 0/1`), and final high-capability review
  are PASS in `/tmp/simple-simple-script-events.5IEatF`. The earlier system
  claim was vacuous; the held repair loads `listen` declarations through
  `BrowserSession` and dispatches only through its canonical
  `dispatch_dom_event`, never `inject_dom_event`. Evidence covers exact UTF-8
  target/event/action bounds `2048/2049`, `64/65`, and `4096/4097`; listener
  capacity `256/257`, normalized duplicate identity and tombstone reuse;
  missing-target, unsupported-action, `on*` attribute, and malformed-capture
  rejection; capture/action/default ordering with seven callbacks and executor
  root rebinding; one checkbox default; and canonical Draw IR/Engine2D pixels
  changing from red `0xFFEF4444` to blue `0xFF2563EB`. This bundle is held,
  unexecuted, and unmerged until an admitted current full pure-Simple CLI runs
  its focused SSpec once.
- navigation chrome state patch (2026-07-30): The bundle at
  `/tmp/simple-browser-chrome-state.XRePMs` is HOLD/FAIL at the three-review
  cap. `clear_chrome_pressed_controls` clears the host page owner but does not
  send the existing renderer `begin_pointer(..., false)` cancel/up, so DOM
  pressed state can remain stale; its SSpec checks only the integer clear. All
  other state, paint, hit, drain, projection, partial-wire, and lifecycle work
  reviewed sound but remains unpromoted. The patch is unexecuted and unmerged.
- renderer command capability design (2026-07-30): Origin/main tracing found
  that numeric generation/reply IDs do not establish causal command issuance.
  Startup accepts `ready` while retaining later decoder bytes; after predictable
  init request ID `2` is written, a previously queued valid frame naming reply
  `2` can pass numeric correlation and move the renderer active without proving
  it consumed init. Architecture, TLDR, detail, system-test, and agent-plan
  updates propose fail-closed `SBR2`: one fresh explicit-success
  platform-CSPRNG 128-bit tail capability per host wire, including every
  network response, bound with generation and root/immediate request IDs,
  consumed before broker/frame authority, and retired on every lifecycle exit.
  Network responses also bind the originating renderer fetch wire. The exact
  four-step RED scenario requires `unissued-renderer-reply`, cleanup/restart/
  entropy oracles, a conforming echo control, and ready-buffer defense in
  depth. Status is PROPOSED/UNIMPLEMENTED/RED; no source, spec, manual, build,
  commit, push, or acceptance promotion exists.
  Final cycle-2 freezes common-codec/host-admission/worker-sequencing and
  existing crypto-facade/native-runtime owners; staged authority becomes issued
  only after a complete pending-wire write. The same four steps fold in a
  deterministic split-write oracle, 1 MiB total-budget and canonical i64
  sequence boundaries, stop-versus-close image lifecycle, per-wire entropy
  counters/latency, one transient token allocation, and the selected 10,000
  cycle RSS/latency NFR boundaries. This remains design-only.
- batch-3 reviewed status (2026-07-30):
  - durable Home has production, focused SSpec, canonical generated manual, and
    final normal/high review PASS; it remains held, unexecuted, and unmerged.
  - nonzero-clock JavaScript timers have production, focused SSpec, generated
    manual, and final normal/high review PASS; they remain held, unexecuted,
    and unmerged.
  - `<mark>` has production/spec high review PASS, but its generated manual
    remains FAIL at the three-cycle cap because six raw bullets leak from the
    helper and shutdown text. It is held and unmerged.
  - text overflow remains HOLD/FAIL because CSS-wide cascade resolution is
    unresolved; it is not an implementation-ready patch.
  - iterative DOM tag search has production/spec static high review PASS, but
    its generated manual remains FAIL at the three-cycle cap: only preorder
    assertions were folded. It is held and unmerged.
  The previously recorded SimpleScript PASS and CSS-cascade/bookmark-title
  designs remain unchanged. None of these rows gains executable or merge
  evidence here.
- primary navigation pointer cancellation repair (2026-07-30): A fresh scoped
  cycle replaces the rejected host-only clear with broker-owned
  `pointer_pressed` and `pending_pointer_cancel_event_id` state. Primary chrome
  press and off-target release now call the existing renderer pointer-up wire;
  resource-job contention retains the cancellation and the hosted poll loop
  retries it before bookmark/resize work. The focused modern SSpec asserts the
  press wire, deferred release wire, redundant no-op, busy retention, and exact
  retry event ID. The mirrored manuals were updated structurally by hand
  because the deployed binary is not admitted for docgen; executable and
  generated-doc evidence remain pending and no PASS is claimed.
- parallel HTML/CSS/animation rendering cycle (2026-07-30): commit
  `fb4050c3d2b` lands the bounded `<article>` block default, width/height-led
  `aspect-ratio`, canonical CPU DrawIR outline painting, real SimpleScript CSS
  frame-to-DrawIR/Engine2D evidence, completed-animation frame reuse, and
  identity-matched font metadata without fixture-text probing. Root review
  rejected the first font-size inference until it matched the Engine2D-selected
  face and added an empty-face negative control. Modern SSpecs and complete
  truthful manual mirrors are present; qualified pure-Simple execution and
  docgen remain pending, so no runtime PASS or full HTML/CSS claim is made.
- production browser batch 14 (2026-07-30): commit `15b6727a5ce` integrates
  five independently reviewed static/TDD lanes. Renderer bookmark titles now
  use bounded canonical `SBRF8` evidence bound to generation, reply, and
  committed URL, then survive public remove/re-add and profile/UI reopen.
  Sandboxed renderer launch has hostile loader-environment regression coverage
  through the real empty-environment spawn path. The canonical JS environment
  stack validates lexical parents before allocation and bounds corrupt-chain
  traversal; this is a reclamation prerequisite, not a GC completion claim.
  Site swap clears active and pending pointer receipts before renderer
  replacement, with exactly-once release accounting. Animation shorthand/time
  parsing now preserves last-valid source order and uses saturating clock
  arithmetic with exact fractional/zero/infinite/fill/pause DrawIR/Engine2D
  evidence. Combined static/layout/direct-environment guards passed once.
- batch-14 held-work audit: current main already supersedes the old
  content-visibility GPU guard with the stronger shared O(N) paint-state owner.
  The old SimpleScript listener bundle was reconstructed but withdrawn after
  review: parse-local/reused DOM IDs cannot safely identify detached frozen
  event-path nodes, no public unlisten operation reaches tombstone reuse, and
  aggregate listener/action-byte lifecycle accounting is absent. Correct work
  depends on the planned generation-qualified DOM identity migration; commit
  `07d7476562a` must not merge.
- batch-14 runtime admission: no provenance-qualified Stage-4 full
  pure-Simple CLI exists at or after `05c9f4b8549`. Active artifacts were
  stale-lineage, dirty/unfingerprinted, incomplete, racing, or Stage 2/3 only.
  No browser spec/docgen/runtime PASS is claimed and no seed substitute was
  used.
- production browser batch 15 (2026-07-30): commits `b0f47f6aac0` and
  `d25b474cf0f` integrate five independently reviewed implementation lanes.
  A script-denying CSP now advances the shared monotonic clock before returning
  without JS/SimpleScript callbacks, so CSS animation frames remain live.
  Invalid/missing/empty form methods use selected-profile GET semantics while
  valid-but-unsupported `dialog` fails before network. Web upload consumes the
  same canonical Draw IR composition through Engine2D with actual software
  readback receipt and every-pixel absolute evidence. Details/summary parsing,
  O(N) structural visibility, nested/interactive default actions, cancellation,
  and post-animation suppression now agree. rAF deadlines align to the document
  frame origin, use overflow-safe due/refresh/wakeup math, and remain safe after
  the 1,000-task drain cap at `i64.max`.
- batch-15 SBR2 design repair: the architecture/TLDR/detail/agent/system-test
  plans now reuse the existing `crypto_sffi.random_hex(16)` facade while the
  private hosted parent alone validates with the common protocol validator and
  installs staged/issued authority. Arbitrary random hex grants no authority.
  The subsequent atomic `879f28bc059` change migrates every parent/worker
  command, network, fetch, and frame direction with no mixed SBR1/SBR2
  production fallback. Production source is integrated static-only; runtime
  and 10,000-cycle evidence remain RED.
- batch-15 verification boundary: both integration tranches passed one static
  diff/layout/placeholder/direct-environment guard. No provenance-qualified
  current Stage-4 CLI exists, so focused runtime execution and docgen remain
  unclaimed.
- production browser batch 16 status reconciliation (2026-07-30):
  broker-owned HSTS policy is pushed at `6e7b4517a81`. Generation-qualified
  DOM identity is pushed as design at `ac847fbfb67`; it remains PROPOSED/RED
  and is not implemented. Crash-safe one-use SBR2 renderer capabilities are
  pushed at `879f28bc059`, but evidence is static-only: no runtime PASS,
  10,000-cycle PASS, or complete browser claim is made.
- batch-16 admission and rejected work: Stage-4 admission is NONE; discovered
  artifacts are stale-lineage and cannot support execution or docgen claims.
  The JS VM reclamation candidate was rejected because raw reused IDs lack
  generation-qualified external handles, independent host owners are not
  reference-counted, and numeric ownership is not represented by typed mark
  edges. Those are design prerequisites before GC implementation resumes.
  The prior pre-SBR2 history candidate/design remains rejected. Superseding
  parent history is integrated at `2e188a745d9` on the crash-safe SBR2 base,
  with static/held evidence only. No rejected history or GC patch is imported
  and no implementation-complete claim is made.
- production browser batch 17 reconciliation (2026-07-30): figure UA-margin
  behavior is integrated at `897368fb592` with static/held semantic, Draw IR,
  and pixel evidence. Generation-safe JS reclamation is frozen at
  `ef90c16b194` as PROPOSED/RED design only. Live post-listener default-action
  validation is integrated at `ca4769405d6` with static/held evidence.
  The Stage-4 provenance and real-motion wrapper at `6c76b8ac0c0` passes its
  self-tests, but no target runtime is claimed. Capability-bound parent history
  is integrated at `2e188a745d9` with static/held evidence.
- batch-17 admission boundary: Stage-4 admission remains NONE at
  `/tmp/simple-history-h1.d3de` and for the active build, which remains
  stale-lineage. No focused runtime, docgen, 10,000-cycle, implementation
  completion, or full-browser PASS is admitted.
- batch-17 final addendum (2026-07-30): selected-profile `<menu>` UA spacing is
  pushed at `b107a4e2a9e` with static/evidence-held status. G2 reclamation
  implementation is BLOCKED with no commit: the operative `std.js.types`
  contract still exposes the raw-i64 ABI and lacks lexical-parent identity,
  generations, free-list state and counters, typed edges, and external-root
  ownership; its expected symbol contract does not match the repository.
  Resumption requires the repository-wide A-through-E migration. The
  `ef90c16b194` generation-safe GC design remains PROPOSED/RED. No goal
  completion or runtime PASS is claimed.
- production browser batch 20/21 reconciliation (2026-07-30): exact source
  HEAD `08de37b0902b3d703f3d1731ba2f44dc6c18b1a9` includes ten bounded
  static/TDD repairs. Stop retires parent pointer ownership after command
  admission (`a05a0e96e3e`); CSS animation synthesis uses the underlying value
  for omitted per-property endpoints (`0e4b75b167b`); `<time>` remains in
  canonical inline flow (`7b290473ae6`); JavaScript Promise microtasks drain
  through a FIFO cursor (`055605e866c`); hosted pointer input suppresses
  effectively disabled controls while preserving the first-legend exception
  (`55a5e9552b2`); history traversal restores bounded serialized form state
  while Reload rebuilds committed source (`d78e613f3d2`); pending JavaScript
  timers use nextTick/deadline/creation-id heap order (`cbb8027d556`); HTTPS
  303 preserves GET/HEAD and rewrites other methods to GET
  (`fb451aa9914`); bookmark-list mutations publish revision-qualified snapshot
  identities while logical no-ops remain stable (`a95537545d3`); and logical
  sizing maps through the final writing-mode axis before canonical Web layout,
  Draw IR, and Engine2D (`08de37b0902`). All ten rows remain static/unexecuted;
  no qualified runtime, docgen, performance, aggregate HTML/CSS, full-browser,
  or goal PASS is claimed.
- batch-20/21 held and rejected work: D3 generation-qualified DOM dispatch is
  HELD/STOPPED/UNCOMMITTED on one remaining `document_route`
  optional/non-optional type blocker; it has no accepted SSpec, manual, merge,
  or PASS. Security candidate `921fd1` is REJECTED/P0 because renderer
  authority is renewable rather than one-use; it is not pending or accepted.
  Stage-4 admission remains NONE and no runtime claim is made.
- production browser batch 22/23 reconciliation (2026-07-31): exact source
  HEAD `8372ca9607fb6f6ee8fda40c19ff3f573350bbe4` contains seven further
  bounded web repairs. Redirect downgrade checks trust the request scheme
  instead of response-controlled text (`4a141af30d5`); selected address text
  clears on Backspace across every hosted route (`5f0758db126`); flex wrapping
  includes column gap in the wrap threshold (`d620217fb0c`); mixed content is
  rechecked after a trustworthy loopback redirect (`59cbfff9857`); finite
  animation terminal artifacts remain reusable without becoming untimed cache
  entries (`1671c187b9f`); exact `InputEvent` data and input type survive
  dispatch (`c2013e78545`); and address URL references resolve against the
  committed document before crossing the worker boundary (`8372ca9607f`).
  All seven are INTEGRATED but STATIC/EVIDENCE-HELD. Intervening compiler, GPU,
  and documentation commits are concurrent ancestry only; this browser
  reconciliation neither reviews nor claims them.
- batch-22/23 rejected and stopped work: animation lifecycle candidate
  `47df593f600` is REJECTED and is not in `origin/main`; its traceability edits
  must not be imported. Cookie authority candidate `921fd1` remains
  REJECTED/P0, while the distinct cookie-authority protocol repair is
  STOPPED/UNCOMMITTED. D3 generation-qualified DOM dispatch remains
  HELD/STOPPED/UNCOMMITTED. Iframe sandboxing remains an architecture RED gap:
  the current Draw IR embedding design leaves child script sharing,
  navigation, and input unsupported and defines no child sandbox-origin or
  broker-capability contract. Stage-4 admission remains NONE. No runtime,
  docgen, performance, aggregate HTML/CSS, full-browser, or goal PASS is
  claimed.
- production browser batch 24/25 reconciliation (2026-07-31): composition base
  `745e12de62dded9dab51e023e316649df2c1394f` contains ten accepted bounded
  repairs or evidence updates after the batch-22/23 source head. Collapsed
  table borders prefer width before style (`d01ff82c92a`); reset inputs are
  exposed through canonical UI access (`8ce17d741ca`); the canonical window
  renderer manual is reconciled (`df30337b6b1`); resolved image opacity is
  cached without changing opaque/translucent pixels (`7fa1a11ff3c`); Home
  publishes its admitted pending address (`764bc1bdfa6`); TLS failures are
  classified without leaking platform detail or replacing committed state
  (`25b8f352e72`); JavaScript writes before an error remain committed
  (`f44a0122b91`); unsupported link targets fail closed (`f0a222d8695`);
  document UI identities are revision-qualified (`93e8716bcd5`); and response
  bodies reject a second consumer (`7574cd2e1a8`). All source/spec/manual rows
  remain STATIC/EVIDENCE-HELD; the manual-only row adds no execution evidence.
- batch-24/25 active RED boundary: fixed positioning is ACTIVE/UNCOMMITTED on
  the exact `9aad7768ebe` base; rejected predecessor `98ec2f997eb` conflates
  fixed/static and transform/relative state, duplicates absolute dispatch, and
  collapses `z-index:auto` with zero. Animation lifecycle candidate
  `47df593f600` remains REJECTED/DO-NOT-MERGE because path-only identity,
  scalar animation state, lossy time arithmetic, unbounded stale tasks, and
  missing cancel/restart/detach controls make it unsafe. Cookie authority
  `921fd1` remains REJECTED/P0 and its distinct protocol repair is
  STOPPED/UNCOMMITTED. D3 is STOPPED/UNCOMMITTED for current origin: its held
  typed dispatcher omits newer InputEvent payload routing, crosses a Lane-2
  owner, and needs an ABI-aware replay. Iframe implementation remains RED;
  design-only GO requires document base/origin/frame generation, a broker-owned
  frame authority, and frame-bound request/navigation schema before child
  runtime work. Current hidden `srcdoc` recursion has no child runtime, script,
  navigation, or input support. Stage-4 admission remains NONE; no runtime,
  docgen, numeric performance, aggregate HTML/CSS, full-browser, or goal PASS
  is claimed.
- production browser batch 26 reconciliation (2026-07-31): source HEAD
  `13273726363` includes two bounded browser repairs after the prior
  composition base. Stop preserves a partial document's focused `draft` input
  and byte selection while retiring transient chrome and isolated authority
  (`a106bc48114`); CORS now preflights unsafe author headers and rejects an
  ungranted cross-origin request before its actual GET (`bf7dfff029a`). Both
  are INTEGRATED and STATIC/EVIDENCE-HELD. The admitted target runner is still
  absent, so neither row has runtime or docgen evidence.
- batch-26 held/rejected boundary: fixed positioning is selected next from the
  existing HTML/CSS traceability row, but remains ACTIVE/UNCOMMITTED/RED;
  animation lifecycle `47df593f600`, cookie authority `921fd1`, and D3 retain
  their existing rejected or stopped classifications. No runtime, docgen,
  performance, aggregate HTML/CSS, full-browser, or goal PASS is claimed.
- layout box content contract system coverage (2026-08-16): the layout/paint
  recovery landed at `81684d8af46` deleted `_paint_box` and ported
  `layout_core.spl` onto the real `BeLayoutBox` shape, but that shape had no
  system-tier statement — only unit coverage of the paint colour helper. Added
  `test/03_system/browser_engine/layout_box_content_contract_spec.spl` (6
  scenarios: positive geometry, zero-inset identity, derived-not-stored
  mutation, over-constrained negative width, pinned `node_id`/tag identity,
  text-box box-model zeroing), mirrored at
  `doc/06_spec/03_system/browser_engine/layout_box_content_contract_spec.md`,
  planned at
  `doc/03_plan/sys_test/browser_engine_layout_box_content_contract.md`, with the
  contract documented in `doc/07_guide/ui/browser_engine_implementation.md`.
  CSS reaches the box through the product's own `BeDomNode.set_style` expander;
  every assertion is an exact arithmetic oracle computed in the spec, with no
  `skip()`, no `pending()`, and no placeholder pass, so the spec fails closed.
  Scenario 3 is the discriminating one: it mutates padding after construction,
  which is the only way to tell a derived content rectangle from a stored one —
  the precise defect shape of `_paint_box`.
  Coverage boundary recorded rather than padded: `_apply_opacity` is excluded
  because unit tier already closes all four branches, `StyleProps` has no
  `opacity` property, and the function has zero product callers, so no
  CSS-to-paint producer exists to integrate against.
  TEST_BLOCKED — the spec has NOT been executed and is not claimed as passing.
  No admitted pure-Simple CLI exists in this tree: the deployed self-hosted
  binary SIGSEGVs on `simple test --help`, re-bootstrap is gated on that same
  binary's bounded test ABI probe, and stage3 `native-build` of a spec fails HIR
  lowering (`unresolved name: __p-1`). See
  `doc/08_tracking/bug/deployed_selfhost_test_subcommand_segv_blocks_bootstrap_2026-08-16.md`.
  No runtime, docgen, or sspec-maintain evidence is claimed; the mirrored manual
  is hand-authored in generated shape pending a docgen run.

## 2026-08-16 — REQ-WEB-BROWSER-014 sandbox gate wiring (Vulkan/sandbox lane)

- **Audit finding.** The Vulkan half of this lane is code-complete and
  binary-blocked: `scripts/check/browser_vulkan_evidence.spl` and
  `check-simple-web-browser-docker-vulkan.shs` are implemented and fail-closed,
  Docker is usable here and `simple-browser-vulkan:latest` is cached, so the
  only missing input is an admitted pure-Simple CLI. Its current
  `SKIPPED (cannot test)` is honest, not a defect. No new Vulkan work was done —
  it would have duplicated already-landed code.
- **Genuine gap closed (sandbox half).**
  `src/runtime/test/rt_browser_renderer_seccomp_allowlist_selfcheck.c`, added
  2026-08-15 with the seccomp deny-list→allow-list fix, was invoked by
  **nothing**: no runner, no spec, no wrapper. Added
  `scripts/check/check-browser-renderer-sandbox-seccomp.shs` (fail-closed;
  no-seccomp kernel and no-C-compiler host both yield `ERROR — nothing was
  checked`, exit 2) plus the step-based SSpec system scenario
  `test/03_system/browser_engine/browser_renderer_sandbox_spec.spl`
  (REQ-WEB-BROWSER-014, cases SANDBOX-N/E/D) and its mirrored manual
  `doc/06_spec/03_system/browser_engine/browser_renderer_sandbox_spec.md`.
- **Evidence, split honestly.** The GATE executed here:
  `PASS — 3 check(s) verified`, including a real `SIGSYS` kill on `socket()`
  through `rt_browser_renderer_sandbox_enter`. That is native C-runtime
  evidence. The SSPEC SCENARIO is **unexecuted** — no admitted pure-Simple
  self-hosted runtime exists on this host and Rust-seed output is not accepted
  for this lane. **REQ-WEB-BROWSER-014 is NOT promoted**; no runtime, docgen, or
  goal PASS is claimed by this entry.
- **Runtime blocker (verified, not inherited).** Only `bootstrap/stage3/simple`
  is non-seed and it core-dumps on a two-line hello-world via both `compile
  --format=smf` and `native-build`. The bootstrap that would replace it is
  blocked by design: `bootstrap-from-scratch.sh` requires a planner-admission-v2
  envelope, and per
  `doc/07_guide/compiler/minimal_bootstrap_configuration_composition.md` the
  non-circular producer for that envelope **does not yet exist**. Confirmed
  empirically — a correctly-formed authorization leaf (reason
  `self-host-convergence-check`, four real SHA-256 bindings) is rejected with
  `bootstrap-policy-error: malformed-or-untrusted-planner-admission-v2` by both
  `--validate-bootstrap-receipt` and a real run. This contradicts
  `.spipe/stage3-segfault-fix/state.md`, whose closure requires exactly that
  transaction; that lane's research note calling
  `scripts/bootstrap/bootstrap-from-scratch.sh` a "stale reference (does not
  exist)" is also wrong — the script is present (112 KB). Critical path for this
  lane and every pure-Simple criterion downstream is building the admission
  producer. Not owned here; not started.
- **Not covered, do not read as covered**: problems 2 and 3 of
  `doc/08_tracking/bug/browser_seccomp_denylist_and_inprocess_unjailed_2026-08-15.md`
  (no namespace/privilege drop; in-process browsers under `src/app/browser/**`
  still evaluate page script unjailed). The gate proves the jail's syscall
  contract, not that every browser surface enters the jail.

## 2026-08-16 (second pass) — sandbox problem 2 implemented + container-verified

- **Implemented** `browser_renderer_enter_namespaces()` in
  `src/runtime/runtime_process.c`, closing problem 2 of
  `doc/08_tracking/bug/browser_seccomp_denylist_and_inprocess_unjailed_2026-08-15.md`:
  unshare `CLONE_NEWUSER` -> write `/proc/self/setgroups=deny`, `gid_map`,
  `uid_map` -> unshare `CLONE_NEWNET | CLONE_NEWIPC`. Runs from
  `browser_renderer_preinit`. Ordering namespaces -> landlock -> seccomp is
  load-bearing: landlock declares `handled_access_fs` with no allow rules
  (kills every write, including `/proc/self/uid_map`) and the seccomp
  allow-list has neither `unshare` nor `openat`.
- **runtime_need**: the jail is a C-runtime-owned property; `chosen_path`
  = `runtime-owned-change` (this IS the runtime owner module).
  `rejected_shortcuts`: (a) hard-failing `sandbox_enter` when namespaces are
  unavailable — rejected because Ubuntu 24.04's
  `kernel.apparmor_restrict_unprivileged_userns=1` would then leave NO jail at
  all on default hosts, strictly worse than seccomp+landlock; (b) trusting the
  posture boolean in the self-check instead of comparing `/proc/self/ns/net` —
  rejected as exactly the false-green this repo keeps hitting.
- **PID namespace deliberately not unshared**: `CLONE_NEWPID` only affects
  children created after the unshare and `RLIMIT_NPROC=0` forbids forking.
  Claiming it would be theatre. Recorded so a later agent does not "fix" it.
- **New evidence**: `src/runtime/test/rt_browser_renderer_namespace_selfcheck.c`
  (fails on a false claim in EITHER direction), driven by the extended
  `scripts/check/check-browser-renderer-sandbox-seccomp.shs`, now
  `PASS — 4 check(s) verified` and printing `sandbox_namespaces=`.
- **Container verification (both postures proven, so the check is not
  tautological):** bare host `unavailable`; `docker run` default `unavailable`;
  `--security-opt apparmor=unconfined` `unavailable`; **`--privileged`
  `active`** with the netns identity genuinely moving
  `net:[4026533421] -> net:[4026533540]`.
- **QEMU: NOT DONE.** No Linux x86_64 qcow2 exists in-tree and `curl`/`wget`
  are blocked by the context-mode rules, so a VM image must be supplied out of
  band. The privileged container exercises the same kernel property, so this is
  a redundancy gap, not a hole. Do not record QEMU evidence for this row.
- **Still NOT promoted.** All of the above is native C-runtime evidence. The
  SSpec scenario remains **unexecuted** — no admitted pure-Simple runtime; see
  the runtime blocker recorded in the previous entry, unchanged. Problem 3
  (in-process browsers unjailed) remains open.
- **Sabotage discipline satisfied (2026-08-16).** Both gate arms proven to bite
  in a scratch tree copy: posture-lie arm -> FAIL `namespaces_active()=true but
  net ns unchanged`; seccomp default flipped to `SECCOMP_RET_ALLOW` (replaying
  the original deny-list defect) -> FAIL `child survived a non-allow-listed
  syscall (fail-open)`. Pre and post runs both `PASS — 4 check(s) verified`.
- **QEMU hard-blocked, not deferred**: no Linux image in-tree, curl/wget
  blocked by context-mode rules, and `/boot/vmlinuz-*` is root-only with no
  passwordless sudo. Needs an image supplied out of band.
- **Problem 3 NOT attempted, deliberately.** Routing `src/app/browser` through
  the broker is pure-Simple code (~3.5k-line `hosted_browser_renderer_process.spl`).
  With no admitted runtime it could not be compiled, tested, or even
  parse-checked, and it sits on a security-critical path guarded today by an
  honest refusal gate. A large blind edit there would risk replacing a correct
  refusal with a silent unjailed render. The single flip-line remains
  `browser_sandbox_worker_routing_available()` in
  `src/app/browser/sandbox_status.spl`.
- **Self-audit 2026-08-16**: the namespace self-check originally verified only
  the net namespace while the change claimed user+net+IPC plus a uid/gid drop —
  3 of 4 claims unproven. Extended to compare all three ns identities (partial
  unshare reported as full isolation now FAILs) and to prove the privilege drop
  via the overflow-uid oracle (unmapped user ns yields 65534). Sabotage arm 3
  (drop the `uid_map` write) bites: `uid/gid inside jail is 65534/0, expected
  0/0`. Verified active under `docker run --privileged`; host remains
  `unavailable`.
- **Problem 3 partial (2026-08-16)**: added `src/app/browser/sandbox_routing.spl`
  (operator-supplied `SIMPLE_BROWSER_RENDERER_WORKER`, fail-closed probe with
  three declared reasons) and split the flip-line into
  `browser_sandbox_render_route_wired()` AND the probe.
  `browser_sandbox_worker_routing_available()` is now their conjunction, so
  supplying the env var alone can never make the browser claim `jailed`.
  Spec: `test/01_unit/app/browser/browser_sandbox_routing_spec.spl`.
  **Render route still NOT wired** — two concrete blockers, both design
  decisions rather than wiring: (a) the broker returns `DrawIrComposition`,
  not `[u32]`, so the app needs an Engine2dCompositorBackend rasterization
  step; (b) the worker arg is dispatched only at `hosted_entry.spl:285`, and
  reaching it from the CLI would import `os.hosted.*` into every `simple`
  invocation's closure. Corrected an agent claim: app->os is NOT forbidden
  (47 files under src/app already import os.*), so layering is not the blocker.
  Narrowing worth keeping: only the SESSION paths execute page script
  (`browser_session_pixels_at_time`, `browser_engine_animated_frames`);
  `browser_render_html_to_pixel_array` is pure parse/layout/paint, so jailing
  targets two functions, not all rendering.
  **NOTE: none of this .spl is executable here** — no admitted runtime, so the
  new module and spec are unverified code, not a pass.

## 2026-08-16 — REQ-WEB-BROWSER-014 render route wired, startup failure covered

- `src/app/browser/sandbox_render.spl` routes page markup through the jailed
  worker: broker -> worker -> Draw IR -> `render_draw_ir_composition` -> pixels.
  `browser_sandbox_render_route_wired()` flipped to `true`.
- The blocker that kept it `false` was a FALSE NEGATIVE from the repo's
  `.gitignore`-honouring `grep` wrapper (0 hits vs 20 from `/usr/bin/grep`).
  Rule recorded in `.claude/skills/spipe.md`: absence claims require
  `/usr/bin/grep`, and subagent "not found" results must be re-verified.
- New native check `rt_browser_renderer_startup_failure_selfcheck.c` closes the
  startup-failure acceptance row. Two arms, neither can SKIP, both sabotage-
  proven.
- Gate check count was a hardcoded `4` and is now accumulated; verdict is
  `PASS — 6 check(s) verified`.
- Fail-closed on jail failure: empty buffer, never an in-process re-render.
- **Blocked, not done**: the sandboxed render has never executed. Seed lacks the
  `rt_browser_renderer_spawn_sandboxed` extern; no admitted pure-Simple runtime
  on this host. REQ-WEB-BROWSER-014 stays NOT promoted.
- Diagnostic (seed, not lane evidence): browser runs, GUI window captured under
  Xvfb (64x36, 15 distinct colours, real antialiased glyphs), all three routing
  states report distinct correct reasons.
- Explicitly not claimed: real remote page rendering. The app stubs every URL
  except `simple://home`; real TLS/HTTP is wired only into the hosted browser.
