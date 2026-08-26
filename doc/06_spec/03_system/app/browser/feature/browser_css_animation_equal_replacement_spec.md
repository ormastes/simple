# Equal innerHTML CSS Animation Restart

**Requirements:** REQ-WEB-BROWSER-004, REQ-WEB-BROWSER-005,
REQ-WEB-BROWSER-006, REQ-WEB-BROWSER-007, REQ-WEB-BROWSER-021
**Executable spec:** `test/03_system/app/browser/feature/browser_css_animation_equal_replacement_spec.spl`

## Purpose

An explicit `document.body.innerHTML` assignment replaces descendant element
identity even when its bytes equal the current body markup. Fresh descendants
restart their CSS animations at the replacement clock. Non-structural class or
style mutations retain the existing animation epoch.

## Scenario: restart fresh descendants without restarting style mutations

### Register the browser callback

Open a zero-margin document with a `16px` by `16px` stage animated from red to
blue over `100ms`. Render once to establish animation epoch `0`, then register a
`requestAnimationFrame` callback. The callback assigns a saved, byte-equal body
`innerHTML`, obtains the fresh stage, and registers a once-only click listener.

### Advance the monotonic browser clock

Advance directly to `100ms`. The callback observes frame time `100`; the body
bridge generation advances because explicit content replacement created fresh
descendants, while the old animation instance still records epoch `0` until
the pending reconciliation is rendered.

### Dispatch events and animation frames

Render the replacement frame. The fresh stage starts red at animation epoch
`100`, rather than inheriting the old completed blue frame from epoch `0`.
Dispatch the click listener once; it sets the stage width to `8px`. This normal
style mutation advances the DOM mutation generation without advancing the body
bridge generation.

### Observe updated canonical Draw IR pixels and released resources

Render again and verify that the style mutation preserved animation epoch
`100`. The canonical `html_ast` Draw IR stage is at `(0,0)`, measures `8x16`,
and is red. Engine2D produces an exact `32x24` buffer with 128 red pixels and
640 white pixels, no mismatches, and no skipped command. The once listener,
callback value, event-operation queues, timer tasks, and timer handles are
released. Closing the page clears the runtime, animation instances, and body.
