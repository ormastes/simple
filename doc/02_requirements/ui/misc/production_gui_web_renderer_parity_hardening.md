# Production GUI Web Renderer Parity Hardening Requirements

## Goal

Harden Simple GUI and Simple Web Renderer parity by proving marker-free,
generated `common.ui` widget HTML renders through production renderer paths and
matches Simple Web software, CPU SIMD, and Metal-backed output exactly for the
first production slice.

## Requirements

- REQ-001: Generated GUI HTML must come from real `common.ui` builder and HTML
  widget renderer APIs.
- REQ-002: The production renderer path must reject legacy fixture markers for
  this slice, including exact sample markers, `simple-web-engine2d-*`, known
  font corpus markers, and WM titlebar/content shortcut markers.
- REQ-003: Generated widget HTML must render through
  `simple_web_layout_render_html_pixels`, not the legacy substring heuristic
  renderer.
- REQ-004: The fixture must include text, multiline text, image, and button
  with icon/text content.
- REQ-005: Software, CPU SIMD, and Metal-backed Simple Web Renderer outputs
  must produce full framebuffers with exact pixel parity.
- REQ-006: The evidence must record whether tolerance was used. This slice
  requires `tolerance_used=false`.
- REQ-007: The system spec must fail on fixture marker use, empty framebuffer,
  low color diversity, CPU SIMD mismatch, Metal mismatch, or tolerance use.
- REQ-008: The Electron/Web reference evidence path must load generated GUI
  HTML directly into Electron, capture ARGB pixels, and compare against Simple
  CPU SIMD expected ARGB without using the exact expected-bitmap canvas mode.
- REQ-009: Electron/Web reference evidence must record pass/divergent/fail
  status, mismatch count, checksums, weighted checksums, blur/tolerance policy,
  generated HTML path, expected ARGB path, and captured ARGB path.
- REQ-010: The generated GUI Electron/Web reference gate must fail on
  divergence for this slice; passing evidence requires `mismatch_count=0`,
  matching checksums and weighted checksums, and `blur/tolerance=false`.
- REQ-011: Generated GUI Electron/Web parity evidence must cover a viewport
  matrix including tight, default, medium, and larger sizes so the slice is not
  limited to a single 96x72 proof.
- REQ-012: The slice must provide one aggregate evidence gate that runs the
  Electron/Chrome viewport matrix, backend-executed CPU SIMD/Metal parity, raw
  Metal framebuffer readback proof, and the broader CSS/layout manifest proof.
- REQ-013: The Electron/Web reference evidence must include at least one
  manifest-driven text-free CSS/layout case that renders real HTML through
  Electron and Simple, requires exact pixel parity, and covers style-block
  selectors, content-box width/height, padding, flex row/column, gap,
  margin-left, and compound class selectors.
- REQ-014: The Electron/Web reference evidence must include a text-free
  CSS/layout case that requires exact pixel parity for solid border
  width/color, content-box sizing with border and padding, direct-child
  selectors, descendant selectors, margin-top, margin-left, and out-of-scope
  selector rejection.
- REQ-015: The Electron/Web reference evidence must include a text-heavy
  CSS/layout case that renders real HTML through Electron and Simple, records
  mismatch counts/checksums/artifacts without tolerance, and is tracked
  separately from exact-passing layout cases until the generic Chrome text
  raster/compositing model is implemented.
- REQ-016: The Electron/Web reference evidence must include a text-free
  selector/inline-style case that requires exact pixel parity for direct-child
  compound class selectors, descendant ID selectors, scoped selector rejection,
  and inline style precedence.
- REQ-017: The Electron/Web reference evidence must include a text-free
  attribute-selector case that requires exact pixel parity for attribute
  presence, exact value, prefix, suffix, and non-matching selector behavior.
- REQ-018: The Electron/Web reference evidence must include a text-free
  `box-sizing:border-box` case that requires exact pixel parity for explicit
  outer width/height with padding and borders, while preserving default
  content-box sizing behavior.
- REQ-019: The Electron/Web reference evidence must include a text-free padding
  longhand case that requires exact pixel parity for `padding-top`,
  `padding-right`, `padding-bottom`, `padding-left`, and shorthand-plus-longhand
  side overrides.
- REQ-020: The Electron/Web reference evidence must include a text-free
  asymmetric border-side case that requires exact pixel parity for
  `border-left`, `border-top`, `border-right`, `border-bottom`, and
  `border-width` side shorthand geometry.
- REQ-021: The Electron/Web reference evidence must include a text-free
  `overflow:hidden` case that requires exact pixel parity for ancestor
  padding-box clipping of oversized descendants and later overflowing siblings.
- REQ-022: The Electron/Web reference evidence must include a text-free
  `visibility:hidden` case that requires exact pixel parity for
  layout-preserving paint suppression of hidden boxes and inherited hidden
  descendants.
- REQ-023: The Electron/Web reference evidence must include a text-free
  positioned-layout case that requires exact pixel parity for
  `position:relative` containing blocks, `position:absolute` direct children
  with `left`/`top` offsets from the containing block padding box, and removal
  of absolute boxes from normal flow.
- REQ-024: The Electron/Web reference evidence must include a text-free
  overlapping positioned-layout case that requires exact pixel parity for
  `position:absolute` boxes painting above later normal-flow siblings when no
  explicit `z-index` is present.
- REQ-025: The Electron/Web reference evidence must include a text-free
  positioned `z-index` case that requires exact pixel parity for positive
  `z-index` ordering across overlapping `position:absolute` boxes.

## Remaining Scope

Electron/Chromium parity is now exact for the marker-free generated GUI widget
HTML slice and for CSS box-model/flex/border/nested-selector manifest cases,
including the selector/inline-style, attribute-selector,
`box-sizing:border-box`, padding-longhand, asymmetric border-side,
`overflow:hidden` clipping, `visibility:hidden` paint-suppression,
`position:absolute` relative-containing-block, overlap paint-order, positive
`z-index`, text-raster-track, line-height text-track, and forced DOM text-flow
matrices. The generated-GUI matrix records fixture-specific text normalization
pixels while still requiring exact checksums and zero mismatch. Generic Chrome
text raster/compositing and general production-renderer Chrome corpus parity
remain open for later acceptance slices.
