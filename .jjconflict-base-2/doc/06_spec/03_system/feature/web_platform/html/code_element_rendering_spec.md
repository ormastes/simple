# Code Element Rendering

## Status

Handwritten modern SSpec mirror. Qualified pure-Simple execution and admitted
doc generation remain pending.

## Requirements

- REQ-WEB-BROWSER-002: canonical HTML semantics
- REQ-WEB-BROWSER-004: Draw IR and Engine2D pixel output
- REQ-WEB-BROWSER-021: bounded production behavior

## Scope

The selected UA profile gives an authored `<code>` element
`display:inline` and `font-family:monospace`. The existing Web semantic
projection, font resolution, `DrawIrComposition` text command, and Engine2D
executor remain the only rendering path. No code-specific painter, font cache,
or IR command is introduced.

The explicit `span { font-family:monospace }` control must match the `<code>`
geometry, resolved font identity, and full Engine2D frame. An authored
`code { font-family:sans-serif }` override must match the normal span control
and differ from the UA-default monospace result.

## Scenario: selected code monospace rendering

1. **Parse code as an inline body child**
   - Build the canonical DOM and confirm `body > code` parentage.
2. **Resolve the code user-agent monospace family**
   - Confirm the default and explicit control resolve `monospace`, preserve
     inline flow, and share geometry.
   - Confirm authored `sans-serif` wins and changes the text width.
3. **Emit canonical code text Draw IR**
   - Confirm `tag=code`, `display=inline`, the resolved font family/identity,
     text parent `target`, and absolute text origin `(0,0)`.
4. **Render monospace code through Engine2D**
   - Require zero skipped commands, full-frame equality with explicit
     monospace, a discriminating diff from sans-serif, and equality between the
     authored override and normal span control.

## Evidence boundary

Executable source:
`test/03_system/feature/web_platform/html/code_element_rendering_spec.spl`.
This is bounded source/spec/manual evidence only. It does not claim every
phrasing tag, every platform font installation, native GPU parity, qualified
runner execution, or full HTML conformance.
