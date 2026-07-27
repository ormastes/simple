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

## Still unsupported

All other scenarios in the executable spec intentionally remain explicit
failure placeholders: TLS and certificate identity, origin/CORS/CSP/redirect
and mixed-content policy, cookies/storage, hostile Node capabilities,
data/javascript/custom/external scheme policy, malformed/late/duplicate/
oversized renderer messages, renderer crash/resource/restart containment, and
conformance/fuzz corpus accounting.
