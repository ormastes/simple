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

## Fixed CSS image background evidence

REQ-WEB-BROWSER-003/004 require one resolved two-color image to pass through
canonical web semantic/layout, Draw IR, and Engine2D software readback.

1. Render an element at `x=3` with a fixed repeating background.
2. Require Draw IR tile origin `(0,0)` and element clip `x=3,width=4`.
3. Scroll by one pixel and require the fixed tile to remain at `y=0` while the
   element shape moves to `y=-1`; the scroll-attached control moves its tile.
4. Require the first fixed pixel to use the viewport-relative blue stripe while
   the scroll-attached control starts with the element-relative red stripe.
5. Require fixed `no-repeat` outside the tile to retain the green background.
6. Require `local` attachment to stay unsupported until element-scrollport
   offsets enter canonical layout.

The scenario was written before implementation. Pre-fix RED is source-semantic:
the lowering rejected non-`scroll` attachment, so its first fixed-command
oracle necessarily failed. It was not run because the current pure-Simple
runtime is unhealthy; no bootstrap or seed fallback was used.

## Canonical Draw IR semantic parentage

REQ-WEB-BROWSER-003/004 require web semantic ownership to survive lowering
instead of becoming an unrelated flat command list.

1. Lower `page -> clip -> bottom/middle/top` with stable element IDs.
2. Require each main command to name its DOM parent's component ID.
3. Require the overflow-hidden ancestor to clip the top command to `16x12`.
4. Require computed `z-index: 1/2/3` to produce stable bottom/middle/top paint
   order despite opposite document order.
5. Encode/decode the composition through the hosted SBRF frame gate and
   require the top command's `parent_id="clip"` to survive.
6. Replay that same `DrawIrComposition` through Engine2D and require only the
   clipped top color in the overlap.

The scenario was authored before implementation. Its pre-fix RED is
source-semantic: every HTML box/text/image constructor retained the Draw IR
default `parent_id=""`; after lowering was fixed, the hosted codec still
rejected every nonempty parent as `unsupported-extended-command`. The central
emission loop now assigns DOM parent IDs to main commands and the owning element
ID to synthetic image/input overlays. The existing Draw IR v2 SDN encoder and
decoder already serialize and restore `parent_id`, so the canonical validator
now admits that bounded semantic metadata without a protocol fork.
Execution and doc generation remain blocked by the unhealthy deployed
pure-Simple runtime; no bootstrap or Rust-seed result is claimed.

## Retained callable DOM event evidence

REQ-WEB-BROWSER-005/006/007/008 require retained JavaScript callables and
inline handlers to use one capture, target, bubble, cancellation, and
default-action path while preserving Simple Script document state.

1. Open a live BrowserSession document seeded by Simple Script.
2. Dispatch document/window custom events and require their target listeners.
3. Dispatch a button click and require window/document/ancestor capture,
   target capture, the inline handler, target bubble, and ancestor/document/
   window bubble in exact order.
4. Add and remove the same listener 300 times, then require only live listeners,
   `preventDefault`, and no link navigation request.
5. Require `stopImmediatePropagation` to suppress the later target listener and
   all bubbling, then require a queued `requestAnimationFrame` callback.

This scenario was authored before implementation and is intentionally RED.
The current JavaScript runtime exposes host-to-JavaScript `call` only;
JavaScript `dispatchEvent()` cannot synchronously enter the canonical
`be_dom_dispatch_event_path`. Doc generation and execution remain blocked by
the unhealthy deployed pure-Simple runtime. No bootstrap, seed fallback,
asynchronous event queue, or second JavaScript dispatcher was used.

## Forced HTML line-break evidence

REQ-WEB-BROWSER-002/003/004 require `<br>` to remain in the inline formatting
context while forcing exactly one new line through canonical Draw IR.

1. Render `alpha<br>beta` with an explicit 20 px line height.
2. Require ordered `alpha` and `beta` Draw IR text commands with inherited
   inline display and 20 px computed line height.
3. Require the semantic-layout `br` box to have zero width and 20 px height.
4. Require `beta` to restart at `alpha`'s x coordinate exactly 20 px lower.
5. Require author CSS `display:none` to suppress the forced break.
6. Only after those semantic and geometry checks, compare Engine2D software
   pixels against the single-line `alpha beta` control and require a change.

The scenario was written before implementation. Pre-fix RED is
source-semantic: `br` was absent from `is_inline_tag`, so layout treated it as
a one-pixel block between inline runs. It was not executed because the current
pure-Simple runtime exits with signal 139; no bootstrap or Rust seed was used.

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
