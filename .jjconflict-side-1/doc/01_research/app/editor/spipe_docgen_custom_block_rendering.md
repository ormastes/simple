# Local Research: SPipe Docgen Custom Block Rendering

**Date:** 2026-05-28
**Status:** Implemented slice

## Findings

- `src/app/spipe_docgen/spipe_docgen/parser.spl` owns scenario body extraction.
  It already dedents `it` bodies and can decide how each body is shown in markdown.
- `test/03_system/feature/usage/math_blocks_spec.spl` uses custom math blocks as `m{ ... }`.
  Those examples need rendered documentation, not only raw source.
- `std.math_repr` provides the rendering logic used by math rendering specs:
  `to_text(expr)` and `render_latex_raw(expr)`.
- Markdown can be made switchable without client-side JavaScript by rendering the
  default view first and placing raw source inside `<details>`.

## Decision

Docgen now uses a small custom-block renderer registry in `parser.spl`.
`m{...}` is the first registered renderer. For each detected block it emits:

- raw block text
- normalized text rendering
- raw LaTeX rendering

Raw scenario source remains available in a collapsed `<details>` toggle.
