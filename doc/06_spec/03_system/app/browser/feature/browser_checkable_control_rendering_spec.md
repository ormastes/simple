# Browser checkbox and radio rendering

Executable scenario:
`test/03_system/app/browser/feature/browser_checkable_control_rendering_spec.spl`

The production browser must preserve checkbox and radio checked state through
DOM activation, canonical Web layout, Draw IR, and exact Engine2D pixels.

## Toggle checkbox state, select one radio, and reject disabled activation

Requirements: `REQ-WEB-BROWSER-003`, `REQ-WEB-BROWSER-004`,
`REQ-WEB-BROWSER-007`, `REQ-WEB-BROWSER-008`, `REQ-WEB-BROWSER-021`

1. **Parse the interactive HTML document.**
   Parse one unchecked checkbox, a named radio pair with only the first radio
   checked, and one disabled unchecked checkbox. Confirm their types, group,
   disabled state, and initial checked state. The body owns the accent color;
   each input independently owns a different caret color.
2. **Resolve control semantics and layout.**
   Resolve all four controls to deterministic 14-by-14 boxes and require the
   hit index to return stable authored IDs for enabled controls. Require the
   input's computed accent color to equal its inherited body value, its
   computed caret color to equal the authored input value, and the two fields
   to remain distinct.
3. **Emit canonical Draw IR and event metadata.**
   Require all four stable frame IDs with their exact authored parents and
   full-viewport clips. Both checkbox frames have no radius; both radio frames
   have radius 7, and the checked radio indicator has radius 4, its stable ID,
   exact parent, and full-viewport clip. Require no indicator for unchecked or
   disabled controls and one indicator for the initially selected radio.
4. **Render and interact through the production browser.**
   Check the complete ARGB buffer size plus exact checkbox corners, rounded
   radio corners, edges, and centers. Click the checkbox on and off, select the
   second radio, and attempt to click the disabled checkbox. Require exact
   generation-qualified target routes projected to their indexed author IDs,
   exact default actions, exclusive indicators, full-buffer restoration after
   the checkbox round trip, a changed full buffer after radio selection, and a
   bit-for-bit unchanged buffer and state after disabled activation.

Evidence: parsed DOM semantics, Web layout/hit metadata, canonical Draw IR
commands, live browser events, checked state, and full-buffer Engine2D pixel
comparisons. The executable SSpec is folded at the source path above.
