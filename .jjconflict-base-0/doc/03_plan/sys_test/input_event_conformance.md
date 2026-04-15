# Input Event Conformance Suite — Design

Status: draft · Date: 2026-04-14 · Track: sys-test / input parity
Related: `doc/03_plan/gui_drawing_layer_variations.md` (item 7),
         `doc/04_architecture/cross_platform_wm.md`,
         `doc/04_architecture/gui_layer_contract.md`

## 1. Problem

The widget tree (`src/lib/common/ui/widget.spl:16`) declares a single
`UIEvent` enum that every backend must produce, but nothing verifies
that the translation from native input to `UIEvent` is identical across
backends. A rename of `KeyPress` to `KeyDown`, a missing `Shift`
modifier flag after a PS/2 set-2 scancode, a stuck `TouchRelease` on
winit, a reversed scroll sign in the browser wheel bridge, or a dropped
IME composition in Electron would all silently diverge between
`ui.tui`, `ui.browser`, `ui.electron`, `ui.none`, `ui.cli`, and the
SimpleOS compositor. A shared conformance suite replays the same
abstract native events against every backend and asserts the resulting
`UIEvent` stream is byte-for-byte identical. It is the only test that
would catch "`Enter` key reaches TUI focus handler but the DOM bridge
forwards `"enter"` lowercase and the browser breaks".

## 2. Canonical event set

Current `UIEvent` variants (`src/lib/common/ui/widget.spl:17-29`) the
suite must cover:

- **Key class:** `KeyPress(key: text)`, plus mode shortcuts produced by
  keybinding resolution in `src/lib/common/ui/mode.spl:43` —
  `CommandMode`, `NormalMode`, `InsertMode`, `Quit`.
- **Pointer class:** `TouchPress(x, y)`, `TouchMove(x, y)`,
  `TouchRelease(x, y)`. `Action("focus_<id>")` is the canonical "click
  landed on widget" dispatch (`src/lib/common/ui/event.spl:106`).
- **Focus class:** `FocusNext`, `FocusPrev`, `Action("focus_<id>")`.
- **Resize class:** `Resize(width, height)`.
- **Lifecycle / close:** `Quit`, `FileChanged`.

### Variants the suite should flag as missing (recommend adding)

These do not exist in `UIEvent` today but are observable at the
`InputBackend` layer (`os.gui.input_event`) and need to reach widgets:

1. `KeyDown(key) / KeyUp(key)` — `UIEvent` only has `KeyPress`, but
   `KeyEvent.Press` / `KeyEvent.Release` exist at the PS/2 / winit
   layer (`src/os/compositor/hosted_input_backend.spl:211`). Without
   separate down/up events, modifier chording and stuck-key bugs are
   invisible.
2. `Modifier(shift, ctrl, alt, meta)` snapshot, or a `modifiers` field
   on every key variant. Modifier state only lives inside the
   `InputBackend` trait methods (`src/os/compositor/input_backend.spl:25-27`)
   and never reaches the widget tree.
3. `Scroll(dx, dy)` / `Wheel(dx, dy, lines|pixels)`. Completely absent.
4. `PointerMove` distinct from `TouchMove`, plus `PointerEnter` /
   `PointerLeave` for hover.
5. `FocusGained` / `FocusLost` window-level focus (vs widget focus).
6. IME: `ImeComposeStart`, `ImeComposeUpdate(text)`,
   `ImeComposeCommit(text)`, `ImeComposeCancel`.
7. `CloseRequested` as distinct from `Quit`. Today
   `hosted_input_backend.spl:199` forces `EVENT_CLOSE` →
   `KeyEvent.Press(Escape)`, which is a lie the suite should surface.
8. `DoubleClick` / `TripleClick` or a click-count field on `TouchPress`.

Phase 1 of the suite covers the 13 existing variants. Phases 2 and 3
add the 8 proposed variants as they land in the enum.

## 3. Backend scope

| Backend | Native source | Translation site | Injection hook |
|---|---|---|---|
| `ui.none` | in-memory `EventQueue` | `src/app/ui.none/event_queue.spl` | push directly |
| `ui.cli` | line or socket text | `src/app/ui.cli/observer.spl`, `socket_server.spl` | feed stdin/socket bytes |
| `ui.tui` | termios + async_input | `src/app/ui.tui/input.spl`, `async_input.spl`, `backend.spl` | feed fd bytes |
| `ui.browser` | DOM `KeyboardEvent` / `PointerEvent` / `WheelEvent` | `src/app/ui.browser/event_bridge.spl`, `dom_bridge.spl` | call bridge with synthetic event struct |
| `ui.electron` | `ipcMain` messages | `src/app/ui.electron/ipc.spl`, `backend.spl` | deliver IPC frames |
| SimpleOS PS/2 | `Ps2Keyboard` / `Ps2Mouse` | `src/os/compositor/input_backend.spl:44` (`Ps2InputBackend`) | stub driver returns scripted `KeyEvent` / `MouseEvent` |
| SimpleOS hosted (winit) | winit events | `src/os/compositor/hosted_input_backend.spl:177` | stub `rt_winit_*` FFI with scripted events |

`ui.test_api` (`src/app/ui.test_api/handler.spl`) is the existing place
to add a shared "inject event" RPC; the suite reuses that transport
where possible.

## 4. Golden event trace format

Traces are **SPL-constructed SDN files** (per `.claude/rules/language.md`
"SDN for all config/data files"). One trace per scenario. File
extension `.sdn`. Shape:

```
trace:
  name: "key_enter_press_release"
  description: "Pressing and releasing Enter produces KeyPress('enter')"
  steps:
    - native:
        ps2: { scancode: 0x1C, kind: "press" }
        winit: { keycode: 13, pressed: true }
        tui_bytes: [0x0D]
        cli_line: "key:press:enter"
        browser_dom: { type: "keydown", key: "Enter", code: "Enter", modifiers: {} }
        electron_ipc: { channel: "input:key", payload: { type: "down", key: "Enter" } }
      expect:
        - UIEvent.KeyPress(key: "enter")
    - native:
        ps2: { scancode: 0x9C, kind: "release" }
        winit: { keycode: 13, pressed: false }
        # ...
      expect: []   # current UIEvent has no KeyUp
```

A step is the tuple *(native stimulus fan-out, expected `UIEvent`
sequence)*. The fan-out object carries **one entry per backend** — a
backend that receives `nil` skips that step rather than failing. The
loader parses the SDN trace into a `TraceScenario` struct and exposes
`scenario.steps[i].stimulus_for(backend)` and
`scenario.steps[i].expected`.

The shared driver runs each step through the backend under test,
drains its `UIEvent` output, and asserts `drained == step.expected`
with a diff-friendly `format_event` printer. Assertion equality is
done on a canonical `text` rendering of the `UIEvent`
(e.g. `"KeyPress(enter)"`) so enum reshapes across phases don't
require rewriting every trace.

## 5. Injection strategy per backend

- **`ui.none`** — direct. Construct `UIEvent` from the native stub or
  push `UIEvent` values the driver already expects. This backend is
  the *reference oracle* — its stimulus is the `expect` list itself,
  so it can never disagree with itself and serves as a round-trip
  check for the trace loader.
- **`ui.cli`** — drive via `socket_client.spl` against an in-process
  `socket_server.spl`. Trace `cli_line` strings are written to the
  server's line reader; the existing observer translation is exercised
  unmodified.
- **`ui.tui`** — feed a pty / pipe with `tui_bytes`. `async_input.spl`
  reads from a configurable fd; inject by pointing it at a pipe the
  test writes. Escape sequences (arrow keys, function keys) come from
  a lookup table in the trace loader, not hard-coded in the spec.
- **`ui.browser`** — do not stand up a real DOM. Call `event_bridge.spl`
  directly with a synthetic `DomKeyboardEvent` / `DomPointerEvent`
  struct constructed from the trace's `browser_dom` map. This
  requires extracting `event_bridge`'s public entry points into a
  testable shim (`inject_key(e)`, `inject_pointer(e)`) — currently
  they are reached through the DOM bridge. **Phase-2 blocker.**
- **`ui.electron`** — stub `ipcMain` as an in-process channel.
  `ipc.spl` already routes by channel name; the test calls the same
  router with the trace's `electron_ipc.payload`.
- **SimpleOS `Ps2InputBackend`** — build `FakePs2Keyboard` /
  `FakePs2Mouse` that implement the same polling API and return
  scripted `KeyEvent` / `MouseEvent` sequences derived from the
  trace's `ps2` field. `Ps2InputBackend.create` already takes them by
  parameter (`src/os/compositor/input_backend.spl:66`), so no
  production code changes.
- **SimpleOS `HostedInputBackend`** — stubbing `rt_winit_*` externs is
  intrusive on host builds. Recommended approach: introduce a
  `HostedInputBackend::from_stub(event_script: [WinitEvent])`
  constructor behind `#[cfg(test)]` that bypasses the event loop,
  feeding the script directly. Real winit is never opened. Until this
  shim lands, mark winit phase-1 cases as "dry-run only".

## 6. Where the suite lives

Shared traces (one file per scenario, grouped by class):

```
test/system/ui/input_conformance/traces/
    key_enter.sdn
    key_modifier_shift_a.sdn
    pointer_click_at_50_50.sdn
    scroll_up_three_lines.sdn
    resize_800_600.sdn
    close_request.sdn
    ime_compose_nihongo.sdn
```

Shared loader + driver:

```
test/system/ui/input_conformance/driver.spl        # parses SDN, runs step loop
test/system/ui/input_conformance/canonical.spl     # UIEvent text encoder
```

Per-backend spec files, each thin (load traces, call driver with its
injector):

```
test/system/ui/input_conformance/none_spec.spl
test/system/ui/input_conformance/cli_spec.spl
test/system/ui/input_conformance/tui_spec.spl
test/system/ui/input_conformance/browser_spec.spl
test/system/ui/input_conformance/electron_spec.spl
test/system/ui/input_conformance/compositor_ps2_spec.spl
test/system/ui/input_conformance/compositor_hosted_spec.spl
```

Lives under `test/system/` rather than `test/unit/` because several
specs require backend processes (pty, socket server, Electron IPC
stub); the existing `test/unit/app/ui/widget_input_textfield_spec.spl`
stays focused on widget-level logic. BDD-style naming can be added
later per `doc/03_plan/28_bdd_spec.md`.

## 7. Integration with wm_compare

**Parallel harness, not part of `wm_compare`.** `src/app/wm_compare/main.spl`
and `scene_registry.spl` compare rendered *output* (screenshots /
widget tree snapshots) across backends for the same scripted scene.
Conformance here compares *input* translation, which is the mirror
problem: it feeds divergent native inputs and asserts the same
canonical event comes out. Mixing the two blurs responsibility and
makes failures hard to attribute (rendering bug vs translation bug).

The two harnesses should share: (a) the `TraceScenario` SDN schema —
`wm_compare` can consume the `expect` list as a scripted input driver
for its scene registry; (b) the `canonical.spl` event printer so logs
are comparable. Keep them as sibling directories under
`test/system/ui/`.

## 8. Phased rollout

**Phase 1 — Keys only, reference + 2 backends.** Traces cover letter
keys, Enter, Escape, Tab, arrow keys, Quit via `Ctrl+C`. Backends:
`ui.none` (oracle), SimpleOS `Ps2InputBackend` with `FakePs2Keyboard`,
SimpleOS `HostedInputBackend` with the new `from_stub` constructor.
Goal: prove the trace format, loader, and driver work end-to-end
before any backend refactors.

**Phase 2 — Pointer + resize, add browser and tui.** Adds `TouchPress`
/ `Move` / `Release`, `Resize`, and window `CloseRequested`. Extracts
`event_bridge.spl` testable entry points for `ui.browser`; wires the
tui pty injector for `ui.tui`. Adds the missing `KeyDown` / `KeyUp` +
`Modifier` variants to `UIEvent` (or decides they go on `KeyPress`),
and adds a migration trace set that exercises them.

**Phase 3 — Scroll + IME, add electron and cli.** Adds `Scroll`, the
four `ImeCompose*` variants, and `DoubleClick`. Wires `ui.electron`
IPC stub and `ui.cli` socket injector. At the end of phase 3 every
backend in §3 runs every trace in `test/system/ui/input_conformance/traces/`.

## 9. Critical files for implementation

- `src/lib/common/ui/widget.spl` — `UIEvent` enum source of truth
- `src/lib/common/ui/event.spl` — widget event dispatch
- `src/lib/common/ui/mode.spl` — mode-shortcut resolution
- `src/os/gui/input_event.spl` — `KeyEvent` / `MouseEvent` shared enums
- `src/os/compositor/input_backend.spl` — `InputBackend` trait + PS/2 impl
- `src/os/compositor/hosted_input_backend.spl` — winit translation
- `src/app/ui.browser/event_bridge.spl` — DOM → `UIEvent`
- `src/app/ui.test_api/handler.spl` — existing test injection RPC
- `src/app/wm_compare/scene_registry.spl` — parity-harness neighbor
