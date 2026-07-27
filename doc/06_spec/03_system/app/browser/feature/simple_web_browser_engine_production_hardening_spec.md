# Production Simple Browser User Flow

Source: `test/03_system/app/browser/feature/simple_web_browser_engine_production_hardening_spec.spl`

## JavaScript, CSS, and compositor animation evidence

The animation scenario requires `HOSTED_WM_ARTIFACT` and its admitted
`HOSTED_WM_ARTIFACT_SHA256` from the hosted live-window evidence wrapper. It
hashes the exact native artifact built from `src/os/hosted/hosted_entry.spl`
before launch and never falls back to `bin/simple`, source execution, or
another renderer. The canonical evidence wrapper runs this focused scenario;
a standalone environment assertion is not artifact-admission evidence.

1. Start `HostedBrowserRendererProcess` and require its sandboxed worker-ready
   reply within 2,000 ms.
2. Send HTML containing CSS, Simple Script that creates `#stage`, and a
   JavaScript `requestAnimationFrame` callback that changes red to blue.
3. Render both returned `DrawIrComposition` frames through one persistent
   software `Engine2dCompositorBackend`.
4. Require the initial frame to schedule 16 ms, advance to that deadline, and
   poll at most 250 times with a 1 ms interval.
5. Require nonempty Draw IR, red initial pixels, blue advanced pixels,
   different 64x48 buffers, rendered commands, and no next animation deadline.

Missing artifact, launch, frame, poll, or cleanup evidence fails the scenario.
This is subprocess integration evidence; native artifact admission and
installed-production proof remain separate release checks. Other scenarios in
the executable spec retain their explicit fail-closed placeholders.

## Hosted structured navigation evidence

The navigation scenario uses the production `HostedWebContentSession` owner
with two deterministic in-process documents. It renders a red start page,
focuses and edits the address through hosted chrome dispatch, submits with
Enter, and requires the blue target page to render. It then drives Back and
Forward through the same structured browser-session controls and requires the
corresponding red and blue pages after each transition.

This proves hosted HTML/CSS rendering and address, Back, and Forward routing
through `BrowserSession` structured UI access. It does not claim real HTTP,
the installed browser executable, Stop/Reload/Home, bookmarks, or link-click
coverage. Those scenarios retain explicit fail-closed placeholders.

## Hosted form-control event evidence

The form-control scenario renders a red CSS-painted text input through
`HostedWebContentSession`, hits it at its layout coordinates, and requires the
same semantic target for pointer press/release, keyboard down/up, and committed
text. Focus, key, before-input, input, and key-up handlers each publish visible
DOM state; the committed value must be `Ada`. The input handler also activates
a CSS attribute selector, so the final rendered control must be blue.

This proves one hosted text-input flow and its rendered state. Default-action
cancellation, form submission, other control types, and installed-browser
event capture remain explicit fail-closed work.
The canonical live-window wrapper executes this focused scenario with its
admitted self-hosted runner before live-window capture.
