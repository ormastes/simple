# Production Simple Browser User Flow

Source: `test/03_system/app/browser/feature/simple_web_browser_engine_production_hardening_spec.spl`

## Static HTML, CSS, Draw IR, and Engine2D evidence

The static rendering scenario requires the same admitted
`HOSTED_WM_ARTIFACT` and `HOSTED_WM_ARTIFACT_SHA256` contract as the animation
scenario. It starts one sandboxed `HostedBrowserRendererProcess` and submits
the returned `DrawIrComposition` to one persistent software
`Engine2dCompositorBackend`.
The canonical live-window wrapper runs this focused scenario after source-
manifest and artifact admission.

The document uses a positioned `.card` rectangle with a red class background,
then an ID rule that overrides it to blue. It also carries visible `Cascade
text` at an explicit font size. Before cleanup, the scenario records Draw IR
text-command evidence and Engine2D readback; after renderer/backend cleanup it
requires nonempty Draw IR, no backend fallback, a 64 by 48 buffer, more than
1,000 blue pixels, no red pixels, and no animation deadline. Missing artifact,
digest mismatch, launch/frame failure, or cleanup failure is fatal.

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
through `BrowserSession` structured UI access. It does not claim real HTTP or
the installed browser executable; the other controls are proved separately
below.

## Hosted form-control event evidence

The form-control scenario renders a red CSS-painted text input through
`HostedWebContentSession`, hits it at its layout coordinates, and requires the
same semantic target for pointer press/release, keyboard down/up, and committed
text. Focus, key, before-input, input, and key-up handlers each publish visible
DOM state; the committed value must be `Ada`. The input handler also activates
a CSS attribute selector, so the final rendered control must be blue.

This proves one hosted text-input flow and its rendered state. Form submission,
other control types, and installed-browser event capture remain explicit
fail-closed work; default-action cancellation is covered below.
The canonical live-window wrapper executes this focused scenario with its
admitted self-hosted runner before live-window capture.

## Hosted rejected-navigation evidence

The rejection scenario starts from a rendered red page. It submits a
`javascript:` address through hosted address focus, text, and Enter dispatch
and requires denial without a pending request or document replacement. It then
starts a real BrowserSession HTTPS document request, proves a mismatched chrome
press/release cannot activate Stop, performs a matching hosted Stop action,
and requires the stopped request to reject a late successful response.

The prior body and pixel buffer must remain unchanged and red. This proves
BrowserSession pending-request and hosted Stop semantics; it does not fabricate
a native HTTP handle or claim that an HTTP response completed successfully.

## Hosted Reload and Home evidence

The Reload/Home scenario mutates a local hosted document, activates Reload
through hosted chrome, and requires the saved source and red raster to return.
It then configures a registered Home document, activates Home through the same
route, and requires its URL, body, and green raster. No network response is
claimed: both transitions are deliberately synchronous production paths.

## Hosted page-link evidence

The link scenario renders a red page anchor, hits its painted coordinates with
a matching pointer press/release, and requires the semantic `next` target to
navigate to a registered document with a distinct blue raster. This exercises
layout hit-testing, DOM click default action, session navigation, and rendering
without a network mock.

## Hosted Favorite evidence

The Favorite scenario creates `HostedWebContentRegistry` with a real in-memory
SQLite `BrowserBookmarkStore`, enables the profile for one hosted window, and
activates Favorite through registry chrome dispatch. It requires the session
favorite state and profile snapshot to contain the saved URL before cleanly
closing the registry. It does not claim filesystem persistence.

## Hosted default-action cancellation evidence

The cancellation scenario renders a red submit button inside a POST form. It
registers capture and bubble listeners on the live form around the button's
target listener, then requires the production DOM dispatch to report capture,
target, and bubble phases against `profile`, `save`, and `profile` in order.
Each listener calls `prevent-default` without mutating the document.

The same live control is then activated by hosted layout hit-testing and a
matching pointer press/release. The canceled button activation must not submit
the form or enqueue navigation, and the body and pixel buffer must remain
unchanged and red. This uses no alternate controller or network fixture.
The canonical live-window wrapper executes the focused Reload/Home, page-link,
Favorite, default-cancellation, rejected-navigation, and unsupported-content
scenarios with its admitted self-hosted runner before live-window capture.

## Unsupported document content evidence

The unsupported-content scenario starts from a rendered red HTML document,
then commits successful network responses whose declared document types are
`image/png` and a malformed empty MIME value. Both responses contain HTML-like
text that would visibly replace the page if MIME policy were bypassed.

The browser must report the unsupported type, finish both rejected loads
without pending work, and preserve the original body and red pixel buffer. A
missing `Content-Type` remains compatible with existing local fixtures, while
an explicit type is accepted as a document only when its normalized MIME is
`text/html`.
