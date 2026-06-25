# Chrome Text Paint Run Helper Evidence

- status: pass
- scope: famous-site corpus text metrics bridge
- production pixel claim: unchanged

## Summary

The browser text painter now exposes calibrated paint runs for famous-site
corpus text. Each run carries the wrapped line text, production paint origin,
line y position, and calibrated proportional width. This gives the production
renderer a single source for the line/advance model already used by Chrome
metrics diagnostics, without copying font-stack calibration into renderer code.

This does not replace the current rectangle-only production corpus paint path.
The Chrome parity blocker remains text glyph antialiasing/compositing. The
helper is the prerequisite data surface for the next gated painter slice.

## Verification

- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/gc_async_mut/gpu/browser_engine/text_painter.spl test/01_unit/browser_engine/text_painter_spec.spl`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple test test/01_unit/browser_engine/text_painter_spec.spl --mode=interpreter --clean --format json`
- `SIMPLE_LIB=src src/compiler_rust/target/release/simple check src/lib/gc_async_mut/gpu/browser_engine/text_painter.spl test/01_unit/browser_engine/text_painter_spec.spl test/03_system/wm_compare/famous_site_corpus_spec.spl`
- `node tools/electron-shell/verify_famous_site_production_probe.js --sample=site_0_google`

The checks passed. The unit spec now covers a `site_0_google` paint-run
projection with four runs, origin `(8, 8)`, line height `18`, and first-line
width `105`. The production probe remains unchanged at `differentPixels: 2717`,
`layoutTextMatch: true`, and four Simple layout lines, confirming this slice did
not make a new production pixel-parity claim.
