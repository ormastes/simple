# BrowserSession disabled fieldset controls

Executable scenario: `test/03_system/app/browser/feature/browser_fieldset_disabled_controls_spec.spl`

**Docgen:** pending; the available self-hosted docgen runtime is unstable.

1. Open a page with a disabled-fieldset button and text input, plus the first
   legend button in a second disabled fieldset.
2. Confirm the public UI snapshot disables the first two controls.
3. Send click and text actions through `BrowserSession.ui_access_act`.
4. Confirm both return `disabled`, with no callback, state, or pixel change.
5. Confirm the first-legend button remains interactive and receives its click.
