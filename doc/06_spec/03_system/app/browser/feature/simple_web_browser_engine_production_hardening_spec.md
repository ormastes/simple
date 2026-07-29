# Production Simple Browser User Flow

Source: `test/03_system/app/browser/feature/simple_web_browser_engine_production_hardening_spec.spl`

## JavaScript, CSS, and compositor animation evidence

The animation scenario requires `HOSTED_WM_ARTIFACT` and its admitted
`HOSTED_WM_ARTIFACT_SHA256` from the hosted live-window evidence wrapper. It
hashes the exact native artifact built from `src/os/hosted/hosted_entry.spl`
before launch and never falls back to `bin/simple`, source execution, or
another renderer.

1. Start `HostedBrowserRendererProcess` and require its sandboxed worker-ready
   reply within 2,000 ms.
2. Send HTML containing CSS, Simple Script that creates `#stage`, and a
   JavaScript `requestAnimationFrame` callback that changes red to blue.
3. Render both returned `DrawIrComposition` frames through one persistent
   software `Engine2dCompositorBackend`.
4. Advance to 16 ms and poll at most 250 times with a 1 ms interval.
5. Require nonempty Draw IR, red initial pixels, blue advanced pixels,
   different 64x48 buffers, rendered commands, and no next animation deadline.

Missing artifact, launch, frame, poll, or cleanup evidence fails the scenario.
This is subprocess integration evidence; native artifact admission and
installed-production proof remain separate release checks. Other scenarios in
the executable spec retain their explicit fail-closed placeholders.

## Production event and conformance receipts

The WM event-routing wrapper requires a separately admitted Aetheric production
proof and records its real pixel artifact hash, readback source, renderer
producer, pixel count, and checksum beside the existing
HTML/WebIR/DrawIR/Engine2D composition receipt. The positive Electron command
does not disable Chromium sandboxing or GPU support. An explicit diagnostic
launch override emits blocked/unavailable evidence and exits nonzero.
PASS additionally requires the renderer's actual `process.sandboxed` signal
and main-process `app.getGPUFeatureStatus()` readback: sandboxing must be true,
and GPU compositing and WebGL must both report `enabled`. Command-line flags
are never substituted for these runtime receipts.

WPT and Test262 are pinned by immutable upstream revisions in
`test/fixtures/browser/conformance/pinned_manifest.env`. No suite is vendored
and no result is claimed: the manifest is `not-run`, claimed count is zero,
known unsupported scopes remain in `unsupported_ledger.env`, and
`receipt_schema.env` only defines a future real receipt. These contracts do not
satisfy the executable REQ-019 placeholder; it remains fail-fast until a real
pinned run and retained receipt exist.
