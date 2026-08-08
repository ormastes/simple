# Label Element Rendering

## Status

Handwritten modern SSpec mirror. Qualified pure-Simple execution and admitted
doc generation remain pending.

## Requirements

- REQ-WEB-BROWSER-002: canonical HTML semantics
- REQ-WEB-BROWSER-003: selected UA style and author cascade
- REQ-WEB-BROWSER-004: Draw IR and Engine2D pixel output
- REQ-WEB-BROWSER-021: bounded production behavior

## Scope

The selected UA profile gives `<label>` `display:inline`. Author CSS remains
later in the existing cascade, so an authored `display:block` still wins. The
existing HTML tree, Web semantic/style/layout stages, `DrawIrComposition`, and
Engine2D executor remain the only rendering path; no label-specific painter or
parallel IR is introduced.

The positive oracle is an explicitly inline `span` with the same text and red
background. An explicitly block `span` and an authored block `label` are the
negative controls.

## Scenario: selected label inline rendering

1. **Parse label with the row as its immediate parent**
   - Build the canonical DOM and confirm `row > label` parentage.
2. **Apply the inline label default before author CSS**
   - Confirm the default is inline with the authored red background.
   - Confirm an authored `display:block` declaration still wins.
3. **Lower label and following text to exact inline Draw IR geometry**
   - Confirm label and `MID` geometry `[32,8,24,16]` and following `RIGHT`
     geometry `[56,8,40,16]`.
   - Require exact geometry and advance parity with the inline span and
     inequality with the block control.
   - Confirm Draw IR retains `tag=label` and `display=inline`.
4. **Rasterize exact label pixels and discriminating controls**
   - Require zero skipped commands and a complete 128 x 40 framebuffer.
   - Require full-frame equality with the inline span, inequality with both
     block controls, and exact red pixel `0xFFDC2626` at `(55,23)`.

## Evidence boundary

Executable source:
`test/03_system/feature/web_platform/html/label_element_rendering_spec.spl`.
This is bounded source/spec/manual evidence only. It does not claim every
phrasing tag, full label activation behavior, qualified runner execution, or
full HTML conformance.
