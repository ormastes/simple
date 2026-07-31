# Hosted negative-tabindex pointer focus

Status: **DRAFT / EVIDENCE-BLOCKED**

Executable source:
`test/03_system/app/browser/feature/browser_negative_tabindex_pointer_focus_spec.spl`.
No runtime result is claimed until an admitted current pure-Simple runner
executes the scenario.

**Requirements:** REQ-WEB-BROWSER-005, REQ-WEB-BROWSER-007,
REQ-WEB-BROWSER-008

## Scenario: Pointer-focus a negative tabindex control and skip it on Tab

### 1. Open a pointer-focusable control outside sequential Tab order

Open a hosted text control with `tabindex="-1"`, a normal button, and focused
state styling. The control starts red; `[data-focused]` turns it blue. An
inline Simple action and a JavaScript listener independently record focus.

### 2. Press the control and observe focus before pointer release

Press `(4, 4)` through `HostedWebContentSession.dispatch_pointer_at`. Before
pointer release, the exact generation-qualified DOM route must be focused,
`data-focused="true"` and `data-simple-focus="yes"` must be published, and
JavaScript must set the title to `js-focus`.

### 3. Lower focused state through Draw IR and Engine2D

Render the live hosted document through `WebRenderBackend`. Draw IR component
`pointer-only` must have blue `0xFF2563EB`. The software Engine2D executor must
skip no command and produce blue pixels.

### 4. Release the pointer and move sequential focus with Tab

Release on the same control, then send Tab through the hosted keyboard route.
The negative-tabindex route must be excluded from sequential order and the
normal `next` button must become the exact focused route.

<details>
<summary>Executable SSpec</summary>

Source:
`test/03_system/app/browser/feature/browser_negative_tabindex_pointer_focus_spec.spl`

</details>
