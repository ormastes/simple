# Kbd, Samp, and Var Rendering

## Status

Handwritten modern SSpec mirror. Qualified pure-Simple execution and admitted
doc generation remain pending.

## Requirements

- REQ-WEB-BROWSER-002: canonical HTML semantics
- REQ-WEB-BROWSER-004: Draw IR and Engine2D pixel output
- REQ-WEB-BROWSER-021: bounded production behavior

## Scope

The selected UA profile keeps `<kbd>`, `<samp>`, and `<var>` in inline flow.
`kbd` and `samp` use the existing monospace family behavior; `var` uses the
existing italic text style. The canonical Web semantic/layout path emits
`DrawIrComposition`, and the existing Engine2D executor resolves and renders
the text. No `pre` whitespace behavior, tag-specific painter, font cache, or
new IR command is introduced.

Explicitly styled `span` controls must match each selected UA default. Authored
`font-family:sans-serif` and `font-style:normal` declarations must win and
match the normal span control.

## Scenario: grouped UA typography

1. **Parse kbd samp and var as inline body children**
   - Build the canonical DOM and confirm the three tags are direct body
     children with their native semantic identities.
2. **Resolve grouped user-agent typography and author overrides**
   - Confirm inline display, monospace `kbd`/`samp`, italic `var`, matching
     control geometry, and authored sans-serif/normal winners.
3. **Emit canonical grouped typography Draw IR**
   - Confirm tag/display/style metadata, resolved monospace font identity,
     text parentage, and absolute origin `(0,0)`.
4. **Render grouped typography through Engine2D**
   - Require zero skipped commands, exact default-to-explicit frame equality,
     discriminating default-to-override differences, and override-to-normal
     equality.

## Evidence boundary

Executable source:
`test/03_system/feature/web_platform/html/kbd_samp_var_rendering_spec.spl`.
This is bounded source/spec/manual evidence only. It does not claim `pre`
whitespace behavior, every platform font installation, native GPU parity,
qualified runner execution, or full HTML conformance.
