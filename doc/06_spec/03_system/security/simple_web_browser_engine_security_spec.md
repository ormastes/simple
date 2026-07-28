# Production Simple Browser Security Envelope

Source: `test/03_system/security/simple_web_browser_engine_security_spec.spl`

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
