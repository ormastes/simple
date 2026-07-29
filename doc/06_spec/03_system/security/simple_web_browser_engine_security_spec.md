# Production Simple Browser Security Envelope

## Shared secondary-window HSTS evidence

REQ-WEB-BROWSER-011/014 require every hosted browser window to use the same
broker-owned HSTS state rather than a renderer-local or secondary-window store.

1. `Navigate through verified HTTPS` loads one persisted include-subdomains
   policy into the existing hosted renderer registry and requires an HTTP
   subdomain URL to upgrade to HTTPS.
2. `Share secondary-window HSTS through the existing registry` admits a policy
   learned by a secondary broker, requires an HTTPS upgrade, and requires the
   shared state to become dirty.
3. `Persist shared HSTS before every browser window closes` saves that exact
   shared snapshot through `BrowserProfileStore`, clears dirty state only after
   success, reloads it into a fresh registry, and requires the secondary policy
   to upgrade after restart. A closed profile must reject the save, preserve
   dirty state, and still permit bounded registry resource reclamation; the
   hosted owner reports/retries that persistence failure instead of leaking a
   secondary renderer.

The scenario was authored before implementation. Pre-fix RED is structural:
`HostedBrowserRendererRegistry` had no HSTS owner or snapshot API, secondary
renderers started empty, and `hosted_entry` persisted only the primary
renderer. The failed-save branch admits a real sandbox renderer with the exact
hashed `HOSTED_WM_ARTIFACT`, then requires `remove_window` to reclaim it while
the shared snapshot remains dirty. The unhealthy pure-Simple runtime prevents
executing that RED; no bootstrap or seed fallback is used. Live
`advance_window`, retry timing, and wall-clock expiry remain part of the
blocked production artifact gate.

Source: `test/03_system/security/simple_web_browser_engine_security_spec.spl`

## Browser-owned CORS request identity

REQ-WEB-BROWSER-010/012 require the canonical fetch path to derive the actual
cross-origin CORS request's `Origin` from its requester, including after a
redirect. The focused protocol scenario supplies a forged
`Origin: https://attacker.test` alongside an ordinary retained header. Fetch
preparation must remove the forged value, emit exactly the canonical
`Origin: https://app.test`, and preserve the unrelated header.

The scenario was authored before implementation. Pre-fix RED is structural:
`CorsChecker` adds its origin only to preflight requests, while the actual
simple CORS request passes caller headers through unchanged. The unhealthy
pure-Simple runtime prevents executing that RED; no bootstrap or seed fallback
is used.

## Ordered head meta CSP

The `should apply head meta CSP in source order to every active resource`
scenario is requirement-traced executable coverage for the ordered policy
contract. It requires the response-header policy to govern resources before a
head meta policy, each following meta policy to intersect with earlier policy,
and script elements, stylesheets, imports, images, CSS backgrounds, and
redirects to retain the policy applicable at their document position. It also requires
`sandbox`, `frame-ancestors`, and `report-uri` to have no effect when delivered
by meta. The scenario was authored red before the ordered resource plan and
policy snapshots were implemented. The recorded pure-Simple compiler crash
still prevents executable confirmation, so no runtime PASS is claimed.

Dispatchable inline `on*` handlers live in the serialized body after every
valid head meta policy, so they use the final intersected document policy. The
focused handler scenario uses the same `prevent-default` action twice:
`script-src 'none'` suppresses it before canonical dispatch and permits the
anchor default, while `'unsafe-inline'` admits it and cancels that default.

The folded bounds scenario supplies a 4,097-byte meta policy and requires the
loader to fail closed, retain a bounded warning, and dispatch no following
script request. It does not treat malformed policy input as permission.

## Identical image URL admission identity

REQ-WEB-BROWSER-004/012 require resource admission to remain bound to the node
whose source-position CSP allowed it. The scenario uses one URI twice: an
earlier stylesheet background is allowed before meta CSP, while a later inline
background is denied by `img-src 'none'`.

1. Load and retain the earlier one-pixel magenta PNG.
2. Require canonical Draw IR to contain `allowed_background_image`.
3. Require canonical Draw IR to omit `blocked_background_image`.
4. Require Engine2D software readback to contain exactly the four pixels of the
   allowed 2x2 background.

The implementation retains authored DOM/CSS URLs, evaluates CSP before
deduplicating decoded image data, and records one ordered
`BrowserImageSource.render_resource_key` binding per occurrence. Render-only
HTML/CSS lowering replaces allowed occurrences with that opaque key; blocked
occurrences receive a separate non-resource key, so the existing Draw IR image
lookup fails closed without a second renderer or pixel store. Static browser
conformance, rendering-source-coupling, and HTML/CSS traceability gates pass.
The unhealthy pure-Simple runtime still prevents executing the scenario, and
no bootstrap or seed fallback was used.

### DOM mutation identity controls

The follow-up control uses two identical image URLs admitted under opposite
source-position CSP decisions. Their opaque decisions are attached to the
canonical node through the existing NUL-prefixed hidden-attribute seam.
Ordinary DOM and body serialization must still contain only the authored URL
and must not expose either opaque key namespace.

1. Remove the allowed node and require the surviving blocked twin to remain
   absent from Draw IR.
2. Reverse the two nodes and require the allowed image command to remain while
   the blocked command stays absent.
3. Retain a stylesheet-source control proving that stylesheet admission remains
   independent of body-node order.

The renderer-only serializer consumes hidden node bindings directly. The
stylesheet-only binder handles the separate ordered stylesheet source lane; it
does not rematch body nodes by URL or occurrence index.

## Platform renderer sandbox

The `should run the site renderer in the required platform sandbox` scenario is
executable on a Linux host when `HOSTED_WM_ARTIFACT` and its admitted
`HOSTED_WM_ARTIFACT_SHA256` name the current exact native artifact for
`src/os/hosted/hosted_entry.spl`.
The canonical live-window evidence wrapper runs this focused scenario after
source-manifest and artifact admission; a standalone environment assertion is
not artifact-admission evidence.

It creates `HostedBrowserRendererProcess` with generation `41` and a `64x48`
viewport, starts that artifact through the production sandbox launcher, waits
for the real `ready` protocol message, renders a small HTML document, verifies
an `ok` frame with at least one Draw IR batch, then closes the renderer.

The scenario fails closed when the artifact is missing, startup fails, the
protocol/render fails, or the renderer cannot be closed. It does not shell out
or use raw runtime APIs.

## Production file-scheme denial

The `should deny unaudited file navigation through the production broker`
scenario uses the same admitted artifact and SHA-256 contract. It starts and
initializes the real sandboxed `HostedBrowserRendererProcess`, asks its public
broker API to navigate to `file:///etc/passwd`, and requires the existing
`invalid-navigation` denial before any worker command is started. The renderer
is closed on every start, initialization, denial, and cleanup branch.
The canonical live-window wrapper executes this focused denial after source-
manifest and artifact admission.

## Production Node and native API denial

The Node/native denial scenario starts the admitted sandboxed renderer and
loads one visible page that attempts filesystem, child-process, socket,
environment, and IPC access through Node globals, plus an unsupported ambient
Simple Script host command. BrowserSession evaluates the actual page runtime's
`require`, `process`, and `Buffer` visibility once, records each failed hostile
script, and keeps the diagnostics bounded. The worker transports them in the
versioned frame envelope and the host exposes them on
`HostedBrowserRendererResult` without altering Draw IR.

The scenario requires all five hostile scripts to fail, all three Node globals
to be `undefined`, a nonempty rendered composition, and successful renderer
cleanup. The decoder remains compatible with legacy
`SBRF2` frames while admitted worker frames use bounded diagnostic/history
`SBRF4` frames; `SBRF3` remains decode-compatible.
An unchanged frame alone is not treated as denial evidence.

## Production oversized protocol denial

The oversized-text scenario starts and initializes the admitted sandboxed
renderer, then sends a 4,097-byte text action through
`HostedBrowserRendererProcess.begin_text_input`. The existing versioned
protocol encoder rejects it as `invalid-action` at its 4,096-byte text bound,
before a worker write occurs. The renderer closes before the denial assertion.
This is real host-process protocol-boundary evidence, not raw-wire injection;
malformed, late, and duplicate frame injection remain explicit fail-closed
placeholders. SBRF2/SBRF3 frame compatibility is unchanged, while SBRF4 adds
length-delimited current/back/forward URL state for validated browser chrome.

## Production renderer fault containment

The `should contain admitted renderer crash and timeout failures`
scenario exercises two dedicated, framed test controls on the admitted renderer
only after its normal `ready` and `init` lifecycle has reached `active`.

`Crash the admitted renderer after ready` makes the real sandboxed child exit
before it emits a frame. The broker observes `renderer-crashed` through its
ordinary polling path. `Hang the admitted renderer after ready` consumes the
bounded framed command, emits its correlated `test_hang_ready` acknowledgement,
then emits no frame. The broker accepts that acknowledgement only for its
matching pending command; without it the deadline fails as
`renderer-hang-unacknowledged`, preventing a false-green timeout. Only an
acknowledged hang returns `renderer-timeout`, then its existing close path
terminates the child process group. Page HTML and scripts cannot invoke or
observe either control because they have no access to the parent-to-worker
framed stdin channel.

After each exact failure reason, the scenario starts, initializes, renders, and
closes a fresh admitted renderer. This proves crash and timeout cleanup without
using raw process APIs or a generic test transport. Memory and restart-rate
budget evidence remains unsupported.

## Still unsupported

All other scenarios in the executable spec intentionally remain explicit
failure placeholders: TLS and certificate identity, origin/CORS/CSP/redirect
and mixed-content policy, cookies/storage,
data/javascript/custom/external scheme policy, malformed/late/duplicate/
renderer messages, renderer memory/resource/restart-rate containment, and
conformance/fuzz corpus accounting.
