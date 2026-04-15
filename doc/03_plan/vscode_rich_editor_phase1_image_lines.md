<!-- codex-design -->
# VS Code Rich Editor Phase 1 Plan

**Feature:** `vscode_rich_editor`  
**Phase:** `phase1_image_lines`  
**Date:** 2026-04-12

## Scope

Implement only the first shippable phase for the standalone rich editor:

- text lines can embed `img{...}`
- the image renders inside the custom editor
- the rendered image uses dynamic height derived from its intrinsic aspect ratio
- the containing editor line grows with the rendered image

## In Scope

- improve the inline image widget path in `vscode_rich_editor`
- add a sample `.spl` file and sample image asset for manual verification
- build and open the standalone extension in a VS Code extension host

## Out of Scope

- stable block ids
- block-local edit protocol
- duplicate-content collision fix
- multi-editor split support
- full extension test harness

## Implementation Notes

### Rendering model

- keep `img{...}` as a cursor-aware replacement widget
- render the widget as inline content so the surrounding text line owns the
  height increase
- constrain width, not height
- let height be `auto` so the browser computes it from the image aspect ratio

### Safety constraints

- preserve a reasonable max width so lines do not become unusably wide
- keep explicit error fallback for missing images
- do not change math rendering in this phase

## Exit Criteria

- opening the rich editor on the sample file shows an embedded image
- the line containing the image is visibly taller than normal text lines
- moving the cursor into the `img{...}` block reveals raw source again
- missing images still render an error widget
