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
