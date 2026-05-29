<!-- codex-research -->
# SimpleOS QEMU Validation Domain Notes

Date: 2026-04-08
Sources:

- QEMU QMP Reference Manual: `https://www.qemu.org/docs/master/interop/qemu-qmp-ref.html`

## Relevant QEMU Features

### User networking and host forwarding

QEMU's `NetdevUserOptions` supports `hostfwd`, which redirects incoming TCP, UDP, or UNIX host connections to guest endpoints. That is the correct mechanism for per-lane SSH exposure without requiring TAP or admin privileges.

Implication for SimpleOS validation:

- Each concurrent SSH lane should use a unique host port.
- Example allocation:
  - lane A: `hostfwd=tcp::2224-:22`
  - lane B: `hostfwd=tcp::2225-:22`
  - lane C: `hostfwd=tcp::2226-:22`
- The generic `x64-ssh` scenario in `src/os/qemu_runner.spl` hardcodes `2222`; parallel workers should override that in ad hoc commands.

### QMP input automation

QEMU supports `input-send-event` through QMP. That command can send:

- key events
- pointer button events
- relative motion events
- absolute pointer motion events

The QMP documentation includes examples for:

- left mouse button press/release
- key combinations such as Ctrl+Alt+Delete
- absolute pointer moves via `abs` x/y events

Implication for SimpleOS validation:

- Mouse and keyboard validation should not rely on manual interaction.
- For the WM lane, QEMU should be started with a QMP socket, then a driver should send:
  - absolute pointer move
  - left-button press
  - left-button release
  - drag sequence for title-bar movement
  - Alt+Tab or launcher shortcut key sequences

## Recommended Automation Shape

### For SSH / networking

- Use `-netdev user,id=n0,hostfwd=tcp::PORT-:22`
- Keep one unique `PORT` per VM instance.
- Probe host readiness with:
  - TCP connect check first
  - then `ssh -p PORT ...` with strict timeouts

### For GUI / mouse

- Add `-qmp unix:build/os/qmp-<lane>.sock,server=on,wait=off`
- Use `input-send-event` instead of manual interaction.
- Keep one unique QMP socket and one unique serial log per lane.

### For evidence collection

- One serial log per lane.
- One QMP socket per lane.
- One hostfwd port per network lane.
- One screenshot or framebuffer capture artifact per GUI lane when possible.

## Validation Impact

Without QMP-driven input injection, SimpleOS can only prove:

- boot reached GUI code
- PS/2 input initialized
- compositor rendered at least one frame

With QMP-driven input injection, SimpleOS can prove:

- click-to-focus
- drag-to-move
- close/minimize interactions
- launcher shortcut behavior
- browser app launch from the desktop session
