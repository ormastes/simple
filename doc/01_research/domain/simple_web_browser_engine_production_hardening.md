<!-- codex-research -->
# Simple Web Browser Engine Production Hardening — Domain Research

Date: 2026-07-26

## Selected profile

Feature B is a secure interactive core, not a claim of full modern-web parity.
Every claimed row is pinned and executable; unsupported rows remain visible.

Primary references:

- HTML parsing/rendering: https://html.spec.whatwg.org/multipage/parsing.html
- DOM: https://dom.spec.whatwg.org/
- CSS cascade/layout: https://drafts.csswg.org/css-cascade-5/ and
  https://drafts.csswg.org/css2/
- Flex/Grid/Animations: https://drafts.csswg.org/css-flexbox-1/,
  https://drafts.csswg.org/css-grid-2/, and
  https://drafts.csswg.org/web-animations-1/
- URL/Fetch: https://url.spec.whatwg.org/ and https://fetch.spec.whatwg.org/
- TLS 1.3/service identity: https://www.rfc-editor.org/info/rfc9846/ and
  https://www.rfc-editor.org/info/rfc9525/
- CSP/mixed content: https://www.w3.org/TR/CSP3/ and
  https://www.w3.org/TR/mixed-content/
- UI events/forms/accessibility: https://w3c.github.io/uievents/,
  https://html.spec.whatwg.org/multipage/forms.html, and
  https://w3c.github.io/html-aam/

## Security model

Assume renderer compromise. Run hostile parsing/script in a site-locked OS
sandbox; broker typed network/TLS/storage/file/UI capabilities; enforce
origins, CORS, CSP, schemes, mixed content, cookie attributes, limits, and
crash containment outside the renderer.

Architecture references:

- https://chromium.googlesource.com/chromium/src/+/refs/heads/main/docs/design/sandbox.md
- https://chromium.googlesource.com/chromium/src/+/refs/heads/main/docs/process_model_and_site_isolation.md
- https://chromium.googlesource.com/chromium/src/+/master/docs/security/mojo.md

## Evidence

Pin selected WPT subsets (HTML/DOM/CSS/URL/Fetch/CORS/CSP/forms/events/a11y)
and selected Test262 language/built-in cases. Fuzz HTML/CSS/URL/JS/IPC/state
transitions under sanitizers and retain minimized reproducers.

- https://web-platform-tests.org/test-suite-design.html
- https://chromium.googlesource.com/external/github.com/tc39/test262/+/refs/heads/master/README.md
- https://google.github.io/oss-fuzz/
## 2026-07-29 CSS URL background follow-up

The current CSS Backgrounds Level 3 contract keeps a single-image implementation
honest only when it preserves the full ordering model: background color below
the image, border above it; `background-origin` defines the positioning area,
`background-clip` defines the painting area, percentage positions apply to the
difference between container and image size, and `repeat-x`/`repeat-y` repeat
on one axis only. The implementation therefore uses one canonical image command
with explicit positioning/tile metadata and performs bounded pixel sampling in
Engine2D rather than expanding a small tile into thousands of Draw-IR commands.

Sources:

- https://www.w3.org/TR/css-backgrounds-3/
- https://drafts.csswg.org/css-values-5/#position

## 2026-07-29 HSTS provenance and inline baseline follow-up

RFC 6797 permits learning an HSTS policy only from an error-free response over
secure transport; an `https:` URL spelling is not transport authentication.
RFC 9525 separately requires the application to verify the complete
certificate path and the service identity. The browser broker must therefore
derive HSTS admission from its completed platform-TLS job, never from a
caller-supplied boolean or a mock response.

CSS 2 and the current CSS Inline Layout draft define an empty atomic
inline-block's baseline at its bottom margin edge. Baseline alignment can be
added at the existing inline-run layout owner by shifting the complete atomic
subtree; it does not require a second inline formatter or Draw-IR adjustment.

Sources:

- https://www.rfc-editor.org/rfc/rfc6797.html
- https://www.rfc-editor.org/rfc/rfc9525.html
- https://drafts.csswg.org/css2/#inline-block
- https://drafts.csswg.org/css-inline/#baseline-alignment

## 2026-07-30 sandbox, mixed-content, and navigation refresh

The current standards review preserves three security boundaries for the next
implementation lanes:

1. Treat renderer IPC as attacker-controlled capability requests. A renderer
   may receive only the operation, origin/site lock, request/reply identity,
   and bounded payload authorized by the broker; stale or replayed authority
   must fail before network, storage, navigation, or UI mutation.
2. A trustworthy document must not execute active HTTP subresources. Mixed
   scripts and fetches fail as network errors; eligible passive content may be
   upgraded, but an upgrade failure must not fall back to HTTP. Top-level
   navigation is a separate policy path and must not be confused with a
   subresource exception.
3. HSTS is learned only from an error-free authenticated HTTPS response.
   Known-HSTS hosts terminate on every TLS/service-identity error; neither a
   redirect, renderer claim, mock response, nor user bypass can authorize an
   invalid secure transport.

The selected embedded-content profile must also remain fail-closed. If iframe
sandbox tokens are not fully implemented, the browser must not advertise them
as enforcement. Where implemented, omitted permissions keep opaque-origin,
script, form, popup, and top-navigation restrictions; individual `allow-*`
tokens relax only their named restriction.

Primary sources:

- https://html.spec.whatwg.org/multipage/iframe-embed-object.html
- https://html.spec.whatwg.org/multipage/browsers.html
- https://fetch.spec.whatwg.org/
- https://www.w3.org/TR/mixed-content/
- https://www.rfc-editor.org/rfc/rfc6797.html
- https://www.rfc-editor.org/rfc/rfc9525.html
