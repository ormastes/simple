# Hosted disabled-control pointer suppression

Executable scenario:
`test/03_system/app/browser/feature/browser_hosted_disabled_control_pointer_spec.spl`

The production hosted-content route must suppress user-pointer activation for
form controls made inactive by a disabled fieldset. Script `dispatchEvent`
remains a separate API. The first legend is the HTML exception and stays
interactive.

## Suppress disabled controls and preserve the legend exception

Requirements: `REQ-WEB-BROWSER-007`, `REQ-WEB-BROWSER-008`,
`REQ-WEB-BROWSER-021`

1. **Open fixed hosted controls and capture the initial frame.**
   Render an enabled first-legend button, a disabled button, and a disabled
   checkbox at deterministic coordinates. Confirm an outer disabled fieldset
   still disables a nested-fieldset legend control, while a label itself is
   not misclassified as its associated control. Capture the DOM and full
   Engine2D frame.
2. **Press and release disabled fieldset controls.**
   Route real hosted pointer down/up pairs to a child span inside the disabled
   button and to the disabled checkbox. Require the button pair's exact deepest
   semantic receipt to be `blocked-child`, while effective-disabled resolution
   still reaches its button owner.
3. **Observe no listener state checked state or pixel change.**
   Require zero callbacks, no title/focus/authored-attribute mutation, an
   unchecked checkbox, byte-identical body HTML, and identical full pixels.
4. **Activate the first legend exception.**
   Route the same pointer sequence to the first legend button. Require exactly
   one click callback, the authored title/style state, and green changed pixels.
   Then dispatch a click explicitly through the script event executor and
   require the disabled button child's listener to fire; only user-pointer
   synthesis is suppressed.

Evidence: HTML/DOM state and Engine2D full-frame pixels. The executable SSpec
is folded at the source path above.
