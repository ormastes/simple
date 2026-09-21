# macOS window registration regression

Source: `test/03_system/app/gui/feature/macos_window_registration_spec.spl`.
Requirement: `REQ-GUI-WINIT-MACOS-REGISTRATION`.

This is a live, externally driven SSpec. It creates a 520×360 winit window
through `GuiRenderer`, pumps native events for at most 60 seconds, and requires
successful native presentation, a moved event, a pressed mouse button, and a
pressed Q key. Missing GUI support or missing input fails the assertions.

## Procedure

Use a current pure-Simple GUI runtime and the current `libspl_winit.dylib`.
Run the source through `scripts/gui/macos-gui-run.shs` with
`SIMPLE_GUI_BINARY` selecting that runtime, `SIMPLE_GUI_RUN_SKIP_NUDGE=1`, and
`SIMPLE_GUI_LAUNCHED_PID_PATH` selecting a new PID receipt file. Keep the
launcher output and the application's stdout/stderr.

1. Using the receipt's launched PID, query System Events for the process and
   its windows. Require at least one window. Never select another `SimpleGui`
   process by name.
2. Record its AX position and size in points. Drag a safe point in the titlebar
   with `cliclick` by (+150,+80) points. Require the final AX position to differ
   by exactly (+150,+80). Do not substitute AX `set position` for the drag.
3. Click within its content area and type `q`. Require the SSpec assertions to
   pass, and retain the before/after bounds plus the test result.

The event assertion alone is insufficient evidence of titlebar dragging:
initial window placement can also generate a moved event. Full acceptance
requires the independent AX bounds comparison above. This fixture avoids the
widget showcase's unrelated application startup and unwired button handler.

## 2026-09-21 audit

Source baseline: `6a7a22ddc37`. Both the dynamic winit provider and interpreter
provider already set macOS activation policy Regular. The dynamic provider
also calls `activateIgnoringOtherApps`, `makeKeyAndOrderFront`, and
`orderFrontRegardless`. No further runtime change was justified by the audit.

Live verification is **blocked**, not passed. The installed
`bin/release/aarch64-apple-darwin/simple` reports version `1.0.0-beta`; launched
through the canonical wrapper it exits before creating a window with
`No source file specified for interpret mode`. PID 53971 was no longer visible
to System Events. A separate bounded check, with bootstrap delegation disabled,
identified this installed binary as a Rust bootstrap seed and failed parsing
`src/lib/nogc_sync_mut/io/process_ops.spl` (`expected expression, found Colon`).
It cannot qualify the pure-Simple route. No bootstrap or replacement seed run
was performed. This SSpec has not yet passed parsing or live execution on an
authoritative current runtime.

Previously retained September 17 evidence under
`build/showcase-evidence/2026-09-17-reverify/` records AX bounds changing from
(200,120) to (350,200) and exit after Q. That historical run used a Rust GUI
driver and is not new pure-Simple verification of this fixture.
