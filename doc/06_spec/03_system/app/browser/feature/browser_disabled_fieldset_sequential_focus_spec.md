# Hosted disabled-fieldset sequential focus

Status: **DRAFT / EVIDENCE-BLOCKED**

Executable source:
`test/03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.spl`.
No runtime result is claimed until an admitted current pure-Simple runner
executes the scenario.

**Requirements:** REQ-WEB-BROWSER-004, REQ-WEB-BROWSER-007,
REQ-WEB-BROWSER-008, REQ-WEB-BROWSER-021

## Scenario: Skip disabled controls and preserve the first legend exception

### 1. Open ordered controls inside and outside a disabled fieldset

Open positive-`tabindex` controls around a disabled fieldset. Its first legend
contains an allowed button; its ordinary button, regular input, and second
legend button are disabled. A focusable link inside the fieldset remains
eligible because fieldset disabledness applies to form controls, not every
descendant.

### 2. Move focus to the first legend without visiting blocked controls

Send Tab through `HostedWebContentSession`. Focus must move from `before` to
`legend-button`. Exact semantic targets, generation-qualified DOM focus, and
focus/blur listener receipts prove real hosted event delivery. No blocked
control may receive its hostile focus marker.

### 3. Lower the allowed focus state through Draw IR and Engine2D

Render the live hosted document through `WebRenderBackend`. Draw IR must show
blue `0xFF2563EB` on `legend-button` and baseline gray `0xFF6B7280` on the
blocked button. The software Engine2D executor must skip no command, produce
blue focused pixels, and produce no hostile red focus pixels.

### 4. Continue in both directions without delivering blocked focus events

Continue forward through the allowed fieldset link and outside button, wrap to
the first outside button, then reverse. The positive and regular disabled form
controls must never become the semantic target, receive listener state, or gain
`data-focused`.

<details>
<summary>Executable SSpec</summary>

Source:
`test/03_system/app/browser/feature/browser_disabled_fieldset_sequential_focus_spec.spl`

</details>
