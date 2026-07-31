# Hosted Browser InputEvent Payload

**Requirements:** REQ-WEB-BROWSER-004, REQ-WEB-BROWSER-008,
REQ-WEB-BROWSER-021

This executable scenario proves that committed UTF-8 text and deletion keys
retain their `InputEvent` payload while crossing the hosted browser session,
live DOM, JavaScript listener, Draw IR, and Engine2D boundaries.

## Scenario: Preserve UTF-8 insertion and deletion payloads through pixels

### 1. Open and focus the hosted text control

Open a styled input with value `A`. The adjacent evidence probe begins red.
Focus the input through hosted pointer press and release.

### 2. Commit one UTF-8 insertion with exact InputEvent data

Commit `한` through the hosted text route. The `beforeinput` listener first
changes the live value to `éY` and selection to UTF-8 byte range `2..3`. The
default edit must re-read that state and replace `Y`, producing `é한`; it must
never reuse the pre-listener `A` value or caret. JavaScript must observe
`beforeinput` then `input`, each with `data=한`, `inputType=insertText`, and
`isComposing=false`. The DOM value becomes `é한` and the UTF-8 caret byte is
exactly `5`.

### 3. Delete backward and forward before committing change

Backspace reports `deleteContentBackward`; Delete reports
`deleteContentForward`. Both expose JavaScript `null` deletion data and
preserve event order. Direct JavaScript boolean sentinels require `data ===
null` in both `beforeinput` and `input`. A generic `keydown` sentinel uses
`typeof ... === 'undefined'` to prove `data`, `inputType`, and `isComposing`
were not installed on a non-InputEvent. Blur dispatches one `change` after all
input events without a duplicate.

A second hosted control changes its live value to `éZ` and selection to UTF-8
byte range `2..3`, then cancels `beforeinput`. BrowserSession must retain those
valid listener side effects and selection while applying no default edit,
setting no dirty marker, and emitting no `input`.

### 4. Lower the listener mutation through Draw IR and Engine2D

The JavaScript input listener turns the evidence probe blue only after seeing
the exact insertion payload. Draw IR must retain component `probe` with
`0xFF2563EB`; Engine2D must produce blue pixels and no red probe pixels.

<details>
<summary>Executable SSpec</summary>

Source:
`test/03_system/app/browser/feature/browser_input_event_payload_spec.spl`

</details>
