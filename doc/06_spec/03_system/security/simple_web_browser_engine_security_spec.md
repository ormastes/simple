# Production Simple Browser Security Envelope

Source: `test/03_system/security/simple_web_browser_engine_security_spec.spl`

## Platform renderer sandbox

The `should run the site renderer in the required platform sandbox` scenario is
executable on a Linux host when `HOSTED_WM_ARTIFACT` and its admitted
`HOSTED_WM_ARTIFACT_SHA256` name the current exact native artifact for
`src/os/hosted/hosted_entry.spl`.

It creates `HostedBrowserRendererProcess` with generation `41` and a `64x48`
viewport, starts that artifact through the production sandbox launcher, waits
for the real `ready` protocol message, renders a small HTML document, verifies
an `ok` frame with at least one Draw IR batch, then closes the renderer.

The scenario fails closed when the artifact is missing, startup fails, the
protocol/render fails, or the renderer cannot be closed. It does not shell out
or use raw runtime APIs.

## Still unsupported

All other scenarios in the executable spec intentionally remain explicit
failure placeholders: TLS and certificate identity, origin/CORS/CSP/redirect
and mixed-content policy, cookies/storage, hostile Node capabilities, scheme
policy, malformed/late/duplicate/oversized renderer messages, renderer
crash/resource/restart containment, and conformance/fuzz corpus accounting.
