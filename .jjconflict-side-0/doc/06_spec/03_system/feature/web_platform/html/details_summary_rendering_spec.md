# Details and Summary Rendering

## Status

Handwritten modern SSpec manual. Qualified pure-Simple execution and admitted
doc generation remain pending.

## Requirements

- REQ-WEB-BROWSER-002: canonical HTML semantics
- REQ-WEB-BROWSER-003: CSS layout and rendering
- REQ-WEB-BROWSER-004: Draw IR and Engine2D pixel output
- REQ-WEB-BROWSER-008: canonical DOM event dispatch and default action
- REQ-WEB-BROWSER-021: bounded production behavior

## Scenario: default authored-summary disclosure marker

The authored-summary marker uses the canonical Web layout, Draw IR text, and
Engine2D path. It does not introduce a marker-specific painter or cache.

1. **Parse the authored disclosure summary**
   - Build the canonical DOM and confirm the first authored `summary` is owned
     directly by `details`.
2. **Resolve the default disclosure marker state**
   - Resolve the UA default as `display:list-item` in both closed and open
     states and reserve the 16 px marker slot before authored inline content.
   - Confirm authored `display:list-item` survives the fast declaration
     dispatcher and retains the same marker slot.
   - Confirm author `display:block` wins the cascade, removes that slot, and
     suppresses marker generation.
3. **Emit canonical disclosure marker Draw IR**
   - Confirm the stable child command is `summary::marker`, is a canonical text
     command at absolute origin `(0,0)`, is parented by `summary`, and carries
     exact `closed`/`open` metadata.
   - Confirm its text is `▶` when closed and `▼` when open, while the
     authored `display:block` control emits no marker command.
   - Confirm authored `display:list-item` emits the same closed marker command
     and state metadata as the UA default.
4. **Render exact closed and open Engine2D pixels**
   - Render empty authored summaries so the marker is the only non-white
     content, require non-white pixels for both states and a discriminating
     full-frame diff, require authored `display:list-item` pixels to equal the
     UA-default closed frame, and require an all-white `display:block` control.

## Scenario: disclosure semantics, events, and pixels

1. **Parse details and summary semantics**
   - Build the canonical DOM.
   - Confirm `summary` is a direct child of `details`.
   - Confirm malformed omitted paragraph end tags close before both `details`
     and `summary`.
2. **Render a closed disclosure**
   - Confirm only the first direct summary is laid out and painted.
   - Confirm other content is `display:none`, has zero geometry, emits no Draw
     IR command, and leaves the white control pixel unchanged.
   - Confirm a closed disclosure without an authored summary uses the bounded
     fallback: no synthetic shadow summary and no visible child content.
   - Confirm a `display:block` keyframe cannot reveal closed content after the
     animation cascade.
3. **Open the disclosure through the canonical event path**
   - Dispatch a cancelable bubbling click from a non-interactive descendant of
     the first summary and resolve the exact owning `details`.
   - Confirm the allowed default action is exactly `details-toggle`.
   - Apply it to the canonical DOM, confirm `open`, serialize for rendering,
     and confirm exact green content geometry, Draw IR, and pixels.
   - Confirm `preventDefault` preserves the closed state.
   - Confirm descendant links and buttons retain their nearer navigation or
     activation default action and do not toggle the disclosure.
4. **Render nested disclosure pixels**
   - Confirm an open outer disclosure does not open its closed inner disclosure.
   - Toggle through a non-interactive descendant of the inner summary and
     confirm the inner owner opens without changing the outer owner, while the
     inner purple content gains exact geometry and pixels.

## Evidence boundary

Executable source:
`test/03_system/feature/web_platform/html/details_summary_rendering_spec.spl`.
The producer remains canonical HTML/Web layout to `DrawIrComposition` to the
software Engine2D compositor. This manual makes no claim for keyboard
activation, grouped disclosures, or a synthesized shadow summary.
