# macOS window registration regression

Source: `test/03_system/app/gui/feature/macos_window_registration_spec.spl`.
Requirement: `REQ-GUI-WINIT-MACOS-REGISTRATION`.

This is a live, externally driven SSpec. It creates a 520×360 winit window
through `GuiRenderer`, pumps native events for at most 60 seconds, and requires
successful native presentation, a moved event, a pressed mouse button, a
pressed Q key, and a subsequent native close request. After disposal, staging
and presentation must fail; repeated close must remain safe. Missing GUI
support or missing input fails the assertions.

## Procedure

Use a current admitted pure-Simple full-CLI GUI runtime and the current
`libspl_winit.dylib`. Qualification requires `SIMPLE_GUI_STRICT_EVIDENCE=1`,
`SIMPLE_GUI_BACKEND=metal` (or the admitted Vulkan backend), and
`SIMPLE_GUI_TRUSTED_MANIFEST_PATH` naming its trusted `gui-driver.env`.
Leave `SIMPLE_GUI_ALLOW_RUST_DRIVER` unset. A missing admission manifest,
seed/debug/stage3 executable, mismatched hash, or absent baked winit marker
must fail before launching. Never retry a rejected run with strict mode off.
Run the source through `scripts/gui/macos-gui-run.shs` with
`SIMPLE_GUI_BINARY` selecting that runtime, `SIMPLE_GUI_RUN_SKIP_NUDGE=1`, and
`SIMPLE_GUI_LAUNCHED_PID_PATH` selecting a new PID receipt file. Keep the
launcher output and the application's stdout/stderr.

Require the resulting `macos_gui_run_pid_receipt_v3` to say
`strict_evidence=1`; selected, bundled, and trusted driver hashes must agree,
and launcher/window-owner PIDs and executable paths must agree. The launcher
checks AX registration for this exact PID. A seed-run SSpec pass or a receipt
from another run cannot qualify this scenario.

1. Using the receipt's launched PID, query System Events for the process and
   its windows. Require at least one window. Never select another `SimpleGui`
   process by name.
2. Record its AX position and size in points. Drag a safe point in the titlebar
   with `cliclick` by (+150,+80) points. Require the final AX position to differ
   by exactly (+150,+80). Do not substitute AX `set position` for the drag.
3. Click within its content area and type `q`, then click its native close
   button. Q deliberately does not terminate the loop; closing before the
   required input must fail. Require all SSpec assertions to pass and retain
   the before/after bounds plus the test result. Confirm the PID exits and its
   AX window disappears after cleanup; do not kill it to manufacture success.

The event assertion alone is insufficient evidence of titlebar dragging:
initial window placement can also generate a moved event. Full acceptance
requires the independent AX bounds comparison above. This fixture avoids the
widget showcase's unrelated application startup and unwired button handler.

## Resource and platform review

The loop uses one renderer and scalar event flags, with no accumulated frame
or event history. An 8 ms sleep bounds idle polling; a monotonic 60-second
deadline bounds the interaction phase. Native event handles are released by
`poll_event`; `close` releases window, loop, and provider handles before
assertions. Capture process CPU, peak RSS, launch-to-window duration, and
cleanup duration for the admitted run; pacing alone is not measured performance
or leak proof. Time and sleep use the existing `std.io_runtime` facade.
AX, CGEvent, and winit are explicitly macOS host acceptance boundaries; this
scenario makes no SoSIX portability claim and introduces no runtime provider.

## 2026-09-22 admission status

The root workspace has no canonical
`build/bootstrap/full/aarch64-apple-darwin/provenance/gui-driver.env`.
Live execution remains blocked pending admission. This extension is unexecuted
and does not close the bug or claim a passing runtime test. Related TODO 277's
launcher fixes do not establish this separate live registration/input proof.
The strict launcher was invoked with this fixture, `SIMPLE_GUI_BACKEND=metal`,
the installed release executable, and the missing canonical manifest. It
exited 1 with `trusted manifest admission failed for SIMPLE_GUI_BINARY`, before
launching an application. This validates missing-admission rejection only.

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
