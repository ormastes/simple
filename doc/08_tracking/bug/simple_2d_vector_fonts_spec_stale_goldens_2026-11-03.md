# simple_2d_vector_fonts_spec: 6 of 7 cases fail on stale pixel/cache goldens

- Spec: test/03_system/app/simple_2d/feature/simple_2d_vector_fonts_spec.spl
- Found while closing self_hosted_font_renderer_optional_field_shape_2026-07-11 (the original
  "no field ttf_rasterizer" error no longer reproduces: 0 occurrences in a full run on the seed).
- Failures are value mismatches, not resolver errors: large.max_x 57 vs 63, cache hits delta 21 vs 7,
  Latin-1 checksum 1583504650 vs 306686342, "AA" checksum 693021525 vs 2027554228,
  cache generation not advancing after face replacement (1 vs >1), clip max 29 vs 36.
- Engine2D text now goes through the font_owner/atlas/quad pipeline (engine.spl font-batch);
  the spec's exact goldens and per-glyph hit counts predate it. Needs a decision per case: regenerate
  goldens or fix the generation/entries accounting (case 5 looks like a real counter bug).
- Not fixed here: it is rendering-pipeline work needing pixel review, not a localized lib change.
