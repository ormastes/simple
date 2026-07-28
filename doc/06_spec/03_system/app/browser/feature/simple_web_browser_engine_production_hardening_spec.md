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
