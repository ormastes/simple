# skia behavioral gaps found by unit specs (batch, 2026-09-16)

Date: 2026-09-16

## Observed
Spec-side issues were fixed where stale (colrv1 split-module imports,
icc_writer enum reference, resample empty-list typing, textblob_v2 SkFont
fields); the following failures remain and are implementation-side:

- `colrv1_spec.spl` (4 of 15): format byte 2 decode returns 0 where 16384
  expected; compositor produces all-zero bitmaps (Solid center pixel, two-layer
  SrcOver, PaintGlyph masking).
- `icc_profile_spec.spl` (1 of 6): `text2u32("wtpt")` returns 2004119668; the
  correct big-endian value for "wtpt" is 0x77747074 = 2003789940.
  (`src/lib/skia/feature/color_management/icc_profile.spl:100`)
- `morphology_spec.spl` (2 of 5): erode leaves a lone white pixel at 255
  (expected 0); dilate produces 1 white pixel instead of >=3 (3x3 expected).
- `path_effect_corner_discrete_spec.spl` (1 of 6): collinear path returns 4
  points where 3 expected.
- `raw_rgba_spec.spl` (1 of 6): header length/magic check reads 81 where 80
  expected.
- `stroke_dash_spec.spl` (2 of 5): uniform dash yields 12 sub-segments
  (expected 10); all-off pattern [0,10] does not produce an empty path.
- `ot_layout_apply_spec.spl` (10 of 22): `semantic: class
  'LayoutLookupActivation' has no field named 'flag'` raised from library code
  (spec constructs the class correctly; the `.flag` access is inside
  `src/lib/skia/feature/glyph/ot_parser_layout_apply` paths); MultipleSubst /
  LigatureSubst cluster preservation returns 18446744073709551615 (u64::MAX /
  -1 sentinel) where 15 / 3 expected.
- `ot_layout_gpos_spec.spl` (15 of 28): PairPos format 1/2 application
  returns 0 where 3 / 2 expected.
- `ot_parser_spec.spl` (5 of 53): glyf triangle parse hits `unwrap on None`;
  invalid-size rejection returns `Some(GlyfRasterBitmap(...))` where `None`
  expected; segment-map exact and midpoint interpolation return false;
  gvar header parse hits `unwrap on None`.
- `ot_parser_layout_selector_spec.spl` (3 of 28): duplicate FeatureTags path
  hits array index out of bounds (index 0, length 0); two segment-map
  interpolation examples return false.

## Impact
Skia OpenType layout application, color-font composition, ICC tag decoding,
image morphology, path effects, and dash generation disagree with their pinned
oracles; the affected feature lanes report red in every full-suite run.

## Expectation
Each spec passes as pinned; none of these are spec bugs (values are documented
oracles, e.g. ICC tags are defined big-endian ASCII).

## Unblock condition
Fix the corresponding implementations under `src/lib/skia/feature/`
(glyph layout apply/gpos/parser, color_management, image morphology, path
effects, stroke dash); re-run the ten specs listed above.
