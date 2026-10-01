# HTML/CSS rendering input corpus

This directory imports the original `corpus/` from
`simple_2d_skia_renderdoc_2026-09-25.zip` (SHA-256
`888e8fd562f1ded2e4573ff3aeaddc733bb4d1ee79def3af2d1153decb42d141`,
bundle dated 2026-09-25). It contains
48 HTML cases, eight independent HTML references, a local checker SVG, and an
index. `manifest.json` is the authoritative case inventory. The included
`manifest.sdn` was supplied as an unvalidated format candidate; do not use it
as a rendering result or as the runner's input.

Run the repo-native integrity check from the repository root:

```sh
bin/release/aarch64-apple-darwin/simple test test/03_system/app/ui/feature/html_css_corpus_integrity_spec.spl --mode=interpreter
```

The check parses the JSON manifest in Simple, verifies all 48 source hashes,
source/reference paths and hashes, eight reference files, viewport/DPR, the
local SVG hash, and
the scroll and animation states. It does **not** render a frame or approve any
image baseline. The ZIP's browser screenshots used disabled GPU and are
authoring evidence only. They were intentionally not imported as native
goldens. The `vulkan_parity_status` and `simple_render_status` fields remain
`not-run` until a separate renderer comparison produces verified receipts.

The executable producer scenario is
`test/03_system/app/ui/feature/html_css_corpus_producer_spec.spl`. It hashes
and feeds all 48 sources through computed Web layout, then lowers each
`DrawIrComposition` through the shared `draw_ir_to_ui_ir` boundary. Its
`build/test-artifacts/simple_2d/html_css_corpus_producer.sdn` receipt reports
per-case producer and lowering results. The runner records both Vulkan lanes
as blocked without physical Linux captures; source execution is not a pixel
golden. Case 41's nested `#scroller` position remains explicit state evidence.
Cases 29–30 bind a pinned 80 × 80 derivative of `checker.svg` as an image
resource and record both source and RGBA hashes; this does not qualify general
SVG decoding. Cases tagged
`subpixel` or `transform` are blocked as faithful Web producers until their
fractional geometry and raster transform semantics survive layout and DrawIR.

Cases with `font_requirement: pin-and-hash-fonts-before-parity` require pinned
font files and proof that the selected faces contain the expected glyphs before
image comparisons can be accepted. This corpus distributes no fonts. The
`state` field records nondefault scroll and animation state; a future render
runner must apply it before capture. References are independent HTML pages,
not screenshots, and only the eight cases that name them have reftest oracles.

## Reference and asset provenance

The following SHA-256 values pin the imported reference pages and local image
asset byte for byte. `manifest.json` carries the same values so the executable
integrity check can reject changed inputs. These are input hashes, not render
results or approved pixel baselines.

| File | SHA-256 |
| --- | --- |
| `references/01-solid-boxes.html` | `6f644ae156fec78dfecd7e50e7b5c5f0c59b8396bcd2dd6063a1227b6838ec31` |
| `references/06-rectangular-clip.html` | `ce0a659f466f71494f6672b44ecf4ad7f239652837ac33da78d8d2bb84a558c2` |
| `references/07-integer-transform.html` | `9b6a6bd4df6813385b6b090d957497fe056215ec65bd33f7402c79f06e991413` |
| `references/16-group-opacity.html` | `3e92b0b037d688364dd3006345e95f780fba1649f5fbe1b249b40bfc4a6a0430` |
| `references/21-multiply-isolation.html` | `7280df68f89cdac40b68d14299f555b38a196aebc3dfedb6a2a3129ba212b253` |
| `references/37-flex-gap.html` | `f4c0f69635dd13b293077735c4b957f9695533bdf8e385fd395abb098a38cc48` |
| `references/38-grid-gap.html` | `7f95e230dc2be3cf45e1ee664b2c59f6e65c31a74939f0150bbb8ed3fe11e4d8` |
| `references/40-pseudo-elements.html` | `6b41a44d049ea0723ce8abe57e2dcc29028a3b35b833fda82a4f3a1afb84ca27` |
| `assets/checker.svg` | `b18637420e995e12f4a4278d6f7480d6b32e2c80fefea86c302dfad44eeaa758` |
