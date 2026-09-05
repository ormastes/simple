<!-- codex-research -->
# Domain Research: Reviewable Feature Evidence

## Findings

### Separate machine truth from human presentation

Evidence systems work best when the pass/fail oracle is structured and the
media is an explanation. W3C testing terminology distinguishes programmatic
tests, reftests, and manual tests; visual output comparison is a reftest, not a
replacement for behavioral assertions. Playwright likewise supports screenshot
baselines but warns that rendering varies by OS, browser, hardware, fonts, and
settings. Its trace viewer preserves action, DOM, and network context and is
preferred to standalone video for debugging.

Sources:

- [W3C testing terminology](https://www.w3.org/wiki/Testing/Terminology)
- [Playwright visual comparisons](https://playwright.dev/docs/test-snapshots)
- [Playwright trace guidance](https://playwright.dev/docs/best-practices)

Implication: Simple should verify events, DOM/SGTTI/Draw IR, protocol frames, and
device readback first, then attach still/motion media for review.

### Text evidence needs explicit normalization and masks

GNU Diffutils preserves line boundaries while offering distinct policies for
trailing space, changed amounts of horizontal whitespace, blank lines, and all
space. Playwright ARIA snapshots collapse whitespace but remain order-sensitive
and allow regular expressions for dynamic text. Insta snapshot redactions
replace declared dynamic fields such as timestamps or IDs and can validate the
field shape before replacement.

Sources:

- [GNU Diffutils whitespace comparison](https://www.gnu.org/s/diffutils/manual/html_node/White-Space.html)
- [Playwright ARIA snapshot matching](https://playwright.dev/docs/aria-snapshots)
- [Insta redactions](https://insta.rs/docs/redactions/)

Implication: use an ordered line matcher with a named normalization policy and
typed field masks. Do not globally remove whitespace or silently ignore dates,
versions, and addresses.

### Stable visual evidence requires environment provenance

Playwright stores platform-qualified baselines and waits for consecutive stable
screenshots before comparison. It can mask volatile visual regions and supports
PNG or lossless WebP snapshots. WPT reftests compare a test render with a
reference render and control capture timing for asynchronous content.

Sources:

- [Playwright visual comparisons](https://playwright.dev/docs/test-snapshots)
- [WPT reftest timing](https://lists.w3.org/Archives/Public/public-web-platform-tests-notifications/2017Mar/0289.html)

Implication: manifests need producer/version/host/display/font/backend identity,
dimensions, capture readiness, baseline identity, comparison mode, and checksum.

### Choose formats by evidence role

SVG is appropriate for true vector diagrams/UI assets. WebP supports lossless
still images and animation with broad browser support. AVIF offers strong still
compression and animation but needs fallback consideration. WebM is a video
container and is not guaranteed to render in every Markdown host.

Sources:

- [MDN image format guide](https://developer.mozilla.org/en-US/docs/Web/Media/Guides/Formats/Image_types)
- [GitHub non-code file rendering](https://docs.github.com/en/repositories/working-with-files/using-files/working-with-non-code-files)

GitHub explicitly documents PNG, JPG, GIF, PSD, and SVG rendering, but does not
document AVIF/WebM Markdown playback in the same support list. Therefore:

- canonical pixel baselines: PNG or lossless WebP;
- vector-native evidence: SVG;
- compressed still presentation: AVIF only with PNG/WebP fallback;
- short motion presentation: animated WebP for GitHub-friendly inline review,
  WebM as a linked/local-player artifact;
- machine oracle: event transcript and keyframes, never encoded video bytes.

### Large binary storage needs a policy, not a blanket extension list

Git LFS stores text pointers in Git and binary contents in LFS storage. Adding a
tracking rule does not migrate prior history automatically.

Source:

- [Git Large File Storage](https://git-lfs.com/)

Implication: add AVIF/WebM tracking only if selected, define a size/retention
policy, keep small text/SVG/manifest artifacts in normal Git, and avoid a broad
historical migration in this feature.

### HTML evidence must be inert by default

OWASP recommends text insertion instead of unsafe `innerHTML`, sanitization when
HTML must be rendered, and sandboxed frames for untrusted content. Sandboxed
frames can disable scripts, forms, navigation, plugins, and same-origin access.

Sources:

- [OWASP HTML5 Security Cheat Sheet](https://cheatsheetseries.owasp.org/cheatsheets/HTML5_Security_Cheat_Sheet.html)
- [OWASP XSS Prevention Cheat Sheet](https://cheatsheetseries.owasp.org/cheatsheets/Cross_Site_Scripting_Prevention_Cheat_Sheet.html)

Implication: generated GitHub-facing manuals should show escaped source,
structured DOM assertions, and stills. Optional local preview must use a strict
sandbox and validated paths; raw captured HTML must never be injected into the
manual DOM.

### Reports should attach typed artifacts

Playwright reports expose test steps and typed attachments with a content type.
Attachments are copied to reporter-accessible storage, keeping test cleanup
separate from report retention.

Sources:

- [Playwright HTML reports](https://playwright.dev/docs/intro)
- [Playwright TestInfo attachments](https://playwright.dev/docs/api/class-testinfo)

Implication: SSpec should persist a typed manifest/receipt per run and let
docgen render by MIME/kind rather than infer everything from file suffixes.

### Protocol evidence should link decoded fields to raw bytes

Wireshark models protocol fields with name, type, base, bitmask, and description.
Its tree view links decoded fields to the relevant byte ranges and highlights
those bytes. It also keeps field values distinct from display text.

Sources:

- [Wireshark protocol fields and masks](https://www.wireshark.org/docs/wsdg_html_chunked/lua_module_Proto.html)
- [Wireshark tree items and byte highlighting](https://www.wireshark.org/docs/wsdg_html_chunked/lua_module_Tree.html)
- [Wireshark packet dissection guide](https://www.wireshark.org/docs/wsdg_html_chunked/ChDissectAdd.html)

Implication: a Simple protocol row needs byte offset/range, bit offset/width,
mask, endianness, typed actual/expected values, status, and importance. Human
highlighting should be generated from these fields while exact bytes remain the
machine oracle.

## Recommended domain model

A compact versioned manifest should contain:

- evidence identity: spec, scenario, step, feature, requirement;
- truth: status, required/optional, assertion/checker result;
- provenance: source revision, command, producer/version, host/target/backend,
  timestamp and freshness policy;
- artifact: kind, MIME, canonical relative path, byte size, checksum;
- still: dimensions, baseline, comparison mode/result;
- motion: duration, event/keyframe counts, event transcript, keyframe checks;
- text: normalization and declared masks;
- HTML: sanitization/preview mode and structured DOM checks;
- protocol: raw bytes plus typed field rows.

This is a schema extension of Simple's existing evidence artifact/receipt, not a
new reporting framework.
