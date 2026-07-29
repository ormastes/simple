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

## Retained Simple Script callback evidence

REQ-WEB-BROWSER-005/006 require `text/simple` callbacks to remain callable
after document loading without reopening the denied ambient compiler runner.

1. Register four callback identities in one inline `text/simple` program.
2. Schedule identity 41 through both `requestAnimationFrame` and a timeout,
   then require the same retained body to run at 5 ms and 10 ms.
3. Require a second timeout to mutate live body HTML at 10 ms.
4. Require an interval to mutate the active stylesheet at 15 ms, prove the
   resulting blue box through canonical renderer pixel output, and repeat at
   30 ms on the BrowserSession animation clock without invalidating the
   unchanged stylesheet twice.
5. Cancel a fourth timeout before it fires and require its title mutation to
   remain absent.
6. Require an unsupported `unsafe_eval` command to emit a bounded warning and
   never enter `ScriptRunner.run_script`.

The scenario was authored before implementation. Source now retains bounded
callback bodies in `SimpleScriptExecutor`, schedules them only through its
existing `EventLoop`, and re-enters the constrained BrowserSession evaluator
when due. Execution remains blocked by the unhealthy deployed pure-Simple
runtime; no bootstrap or Rust-seed fallback is used.

### Immediate Simple Script stylesheet finalization

The separate immediate-style scenario proves that a load-time `style_html`
command survives document finalization in the one canonical stylesheet:

1. Load a red author stylesheet before one inline `text/simple` block.
2. Apply a blue `style_html` override from that block.
3. Require the finalized stylesheet to retain the author CSS followed exactly
   once by the script CSS.
4. Render through the canonical browser renderer and require blue pixels with
   no red pixels.

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

## Retained unchanged-frame evidence

REQ-WEB-BROWSER-004/006/018 require the production hosted worker to retain one
canonical semantic render result without adding a second Web IR, parser,
renderer, or HTML-string pixel cache.

1. Initialize one `HostedBrowserRendererWorkerSession` with a static document.
2. Require one document serialization and one parse/CSS/style/layout/paint
   pass, zero reuse, and composition revision one.
3. Advance the worker clock to 16 ms with no due timer or animation work.
4. Require serialize/parse/CSS/style/layout/paint and composition revision to
   remain unchanged while reuse increments exactly once.
5. Close the worker session and require retained node, style, box, and command
   counts to become zero.

The scenario and focused worker/performance assertions were authored before
the retained-session implementation. Source now provides the first exact
slice: `BrowserSession.render_snapshot_since` serializes only a stale
document/style snapshot, and the worker-owned `SimpleWebRenderSession` reuses
the existing semantic/layout/Draw IR result for a visually unchanged frame.
DOM/title, stylesheet, image, viewport, active-animation, scroll, overlay, and
soak invalidation rows remain fail-fast follow-ups; this section does not claim
their stage-selective reuse or NFR-WEB-BROWSER-003 performance. Execution
remains blocked by the unhealthy deployed pure-Simple runtime, and no
bootstrap or Rust-seed result is claimed.

Focused unit prerequisites additionally require image completion and failure
to change the resource revision without serializing unchanged HTML, linked CSS
completion to change the style revision, and close to clear real BrowserSession
resources, bindings, requests, load state, runtime/timers, and overrides.

The modern production-browser scenario
`should invalidate only dirty retained browser render stages` records this
exact functional matrix:

| Change | serialize | parse | CSS | style | layout | paint | composition |
|---|---:|---:|---:|---:|---:|---:|---|
| title or DOM | +1 | +1 | +1 | +1 | +1 | +1 | revision +1; title checksum stable, painted DOM checksum changes |
| stylesheet completion | +1 | +1 | +1 | +1 | +1 | +1 | revision +1 |
| image pixel replacement | +0 | +0 | +0 | +0 | +0 | +1 | revision +1; Draw IR checksum stable because pixels are retained out of band |
| viewport resize | +0 | +0 | +1 | +1 | +1 | +1 | revision +1 |
| active CSS animation | +0 | +0 | +0 | +1 | +1 | +1 | revision +1 and checksum changes |
| scroll or caret blink | +0 | +0 | +0 | +0 | +0 | +1 | revision +1 and checksum changes |
| navigation replacement | +1 | +1 | +1 | +1 | +1 | +1 | revision +1; retained counts replace rather than append |
| unchanged frame | +0 | +0 | +0 | +0 | +0 | +0 | revision/checksum stable; reuse +1 |
| close | — | — | — | — | — | — | retained node/style/box/command counts zero |

Four same-shape navigation replacements must keep each retained count exactly
at its initial document bound before close. These are source-level functional
counter/checksum oracles only. The deployed pure-Simple target remains
unavailable, so the scenario is runtime RED/unexecuted; no timing, RSS,
10,000-cycle, NFR-WEB-BROWSER-003, bootstrap, or Rust-seed evidence is claimed.

Composition checksums are evidence-only and lazy. Rendering updates the
composition revision and invalidates the prior digest but does not serialize or
hash Draw IR. The scenario explicitly calls
`SimpleWebRenderSession.composition_checksum()` only at comparison points;
repeated requests for an unchanged composition reuse the digest cached under
that composition revision.

## Retained callable DOM event evidence

REQ-WEB-BROWSER-005/006/007/008 require retained JavaScript callables and
inline handlers to use one capture, target, bubble, cancellation, and
default-action path while preserving Simple Script document state.

1. Open a live BrowserSession document seeded by Simple Script.
2. Dispatch a button click and require window/document/ancestor capture,
   target capture, the inline handler, target bubble, and ancestor/document/
   window bubble in exact order.
3. Add and remove the same listener 300 times, then require only live listeners,
   `preventDefault`, and no link navigation request.
4. Require `stopImmediatePropagation` to suppress the later target listener and
   all bubbling, then require a queued `requestAnimationFrame` callback.
5. Require listener `this`, `currentTarget`, and `eventPhase` to match the
   current target; require `preventDefault()` to be a no-op when `cancelable`
   is false; and require `currentTarget == null` with `eventPhase == 0` after
   dispatch.
6. Remove a later listener from an earlier callback and require it to be
   skipped, while a listener added by that callback waits for the next event.

This scenario was authored before implementation and remains partially RED.
BrowserSession now retains JavaScript function values for window, document,
and element listeners in a bounded tombstone-reusing registry. Host-originated
events materialize one shared Event object and invoke those callables through
the executor seam in the canonical DOM capture/target/bubble dispatcher;
cancellation therefore affects the same dispatch and its default action.
Synchronous JavaScript-originated `dispatchEvent()` remains explicitly
fail-closed because invoking the host dispatcher from an active interpreter
would require unsafe re-entry, and Simple Script remains command-only rather
than pretending to retain callables. Doc generation and execution remain
blocked by the unhealthy deployed pure-Simple runtime. No bootstrap, seed
fallback, asynchronous event queue, or second JavaScript dispatcher was used.

### JavaScript-originated synchronous dispatch RED row

The separate `should fail closed for synchronous JavaScript-originated
dispatchEvent` scenario proves the current boundary without contaminating the
host-listener PASS evidence. `window.dispatchEvent(...)` returns `false`,
does not invoke the retained callback, leaves document state unchanged, and
records an explicit warning. Delivering that event synchronously remains RED
until the interpreter can enter the host dispatcher without unsafe re-entry.

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

## Secondary address UTF-8 byte-bound evidence

REQ-WEB-BROWSER-009/010 require every browser address editor to enforce the
same bounded input contract without allowing secondary windows to bypass it
with multibyte text.

1. Start a real hosted secondary renderer registry from the admitted production
   artifact and focus its address control through chrome pointer dispatch.
2. Enter exactly 2048 UTF-8 bytes and require one accepted address callback.
3. Re-focus the address control, then enter 2047 ASCII bytes plus `é`, which is
   2049 UTF-8 bytes but only 2048 codepoints.
4. Require the dispatch protocol to return `address-too-long` with no callback.
5. Require both the accepted draft and the committed document URL to remain
   unchanged after rejection, then close the real renderer registry.

The scenario was authored before the implementation fix. Its pre-fix RED is
state/protocol observable: the secondary registry compared codepoint length,
accepted the multibyte overflow, replaced the draft, and reported one callback,
while the primary address editor already enforced the UTF-8 byte limit.
Execution remains blocked by the unhealthy deployed pure-Simple runtime; no
bootstrap or Rust-seed result is claimed.

## Browser chrome navigation protocol evidence

REQ-WEB-BROWSER-009/010 require browser chrome and page navigation to use one
parent-owned controller with correlated renderer commands.

1. Arm Back in one secondary window, then arm Address in another window.
2. Require the old window's late release to emit no callback or navigation,
   while the current window's matching release focuses its address editor.
3. Replace Back with Address in the same window and require the late Back
   release to preserve the newer Address arm.
4. Replace page press with chrome press and chrome press with page press;
   require each stale release to preserve the newer owner and matching release.
5. Edit and cancel the address, requiring the committed startup state to return,
   then require Favorite to route once to its parent-owned persistence path.
6. Decode real `open`, `back`, `forward`, `stop`, `reload`, and `home` command
   wires and require pending history to leave committed history unchanged.
7. Require Stop to revoke the permit and pending document commit.
8. Decode the bookmark snapshot and authorize one page-link document request
   through the existing parent permit.
9. Feed a command from another renderer generation into the production decoder
   and require decoder-only protocol denial.
10. Close an armed registry and require teardown to clear its global press owner.

The scenario was authored before the implementation fix. Its pre-fix RED is
state/protocol observable: pressing chrome in a second window overwrote the
global press owner but left the first entry armed, so a late release to the
first window could still execute its stale control. The registry now has one
global chrome-press owner and clears stale per-window ownership when that owner
changes or is torn down. Execution remains blocked by the unhealthy deployed
pure-Simple runtime; no bootstrap or Rust-seed result is claimed.
