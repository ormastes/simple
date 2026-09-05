# Plan: SPipe Docgen Custom Block Rendering

**Date:** 2026-05-28
**Status:** Implemented

## Goal

When sspec/docgen encounters a custom block with registered rendering logic,
generated markdown should show the rendered form by default and keep raw source
available through a switchable markdown toggle.

## Requirements

- Detect registered custom blocks inside scenario bodies.
- Render the default documentation view from block-specific rendering logic.
- Preserve raw scenario source in a collapsible markdown section.
- Keep the registry extensible for future blocks beyond `m{...}`.
- Continue rendering plain scenarios as raw `simple` code blocks.

## Implementation

- Added `CustomBlockRender` and renderer registry helpers in
  `src/app/spipe_docgen/spipe_docgen/parser.spl`.
- Registered `m{...}` using `std.math_repr.to_text` and
  `std.math_repr.render_latex_raw`.
- Changed rendered-block scenarios to emit rendered content first, then raw
  source inside `<details><summary>Raw scenario source</summary>`.
- Refreshed `doc/06_spec/feature/usage/math_blocks_spec.md` with rendered-default examples.

## Verification

- `SIMPLE_LIB=src bin/simple test --force-rebuild test/01_unit/app/tooling/spipe_docgen_scenario_body_spec.spl`
- `bin/simple compile src/app/spipe_docgen/spipe_docgen/parser.spl`
