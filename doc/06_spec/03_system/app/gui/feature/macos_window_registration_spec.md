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

### Root-bound producer handoff

For the current P0 lane, the producer root is
`/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922`. The launcher,
trusted manifest, full CLI, source imports, and producer verifier must all use
that same root. Using this winit checkout's launcher with a manifest from P0
will be rejected by `macos_gpu_full_cli_gui_admit`; copying the manifest does
not repair its path, source, and provenance bindings.

The canonical producer is
`scripts/check/build-macos-full-cli-gui-provenance.shs --build`. Its required
inputs include the admitted compiler and manifest at
`build/wm-to-i64-bootstrap/stage3/aarch64-apple-darwin/`,
`build/sffi/libspl_winit.dylib`, `libsimple_runtime_wm.dylib`, and
`libsimple_runtime_c_wm.dylib`, plus clean source and an admitted Endpoint
Security collector policy. A newly built general full CLI or a compiler at a
different bootstrap output path is not automatically this admitted artifact.
The P0/provenance owner must resolve the canonical producer inputs; this lane
must not create aliases, manufacture receipts, or run a competing build.

Both producer `--build` and `--verify` call
`macos_gui_history_require_trust_root`. The inspected policy has
`status=unavailable`, `signing_identity=unassigned`, and
`team_identifier=unassigned`. Consequently this regression depends on **both**
P0 artifact admission and the ES lane's signing/entitlement admission. A
successful bootstrap alone does not unblock strict GUI execution.

After those gates and launch monitoring are established, the prepared command
shape is below. This is a handoff, not an executed or passing command. Set
`WINIT_RUN_DIR` to a new evidence directory owned by this lane; retain the
fixture SHA-256 before and after execution. The fixture may remain in this
isolated winit checkout, avoiding source changes to the admitted producer root.

```sh
producer_root=/Users/ormastes/simple-tmp/macos-bootstrap-restart-20260922
winit_fixture=/Users/ormastes/simple-tmp/mac-winit-registration-20260922/test/03_system/app/gui/feature/macos_window_registration_spec.spl
: "${WINIT_RUN_DIR:?fresh absolute evidence directory required}"
sh "$producer_root/scripts/check/build-macos-full-cli-gui-provenance.shs" --verify || exit 1
SIMPLE_LIB="$producer_root/src" \
SIMPLE_GUI_STRICT_EVIDENCE=1 SIMPLE_NO_BOOTSTRAP_DELEGATE=1 \
SIMPLE_GUI_BACKEND=metal SIMPLE_GUI_RUN_SKIP_NUDGE=1 \
SIMPLE_GUI_BINARY="$producer_root/build/bootstrap/full/aarch64-apple-darwin/simple" \
SIMPLE_GUI_TRUSTED_MANIFEST_PATH="$producer_root/build/bootstrap/full/aarch64-apple-darwin/provenance/gui-driver.env" \
SIMPLE_GUI_LAUNCHED_PID_PATH="$WINIT_RUN_DIR/launched-pid.env" \
    "$producer_root/scripts/gui/macos-gui-run.shs" "$winit_fixture" \
    >"$WINIT_RUN_DIR/launcher.log" 2>&1
```

Treat any verifier or launcher failure as terminal for that attempt. Unset
`SIMPLE_GUI_ALLOW_RUST_DRIVER`; never retry without strict evidence. Retain
the launcher-selected stdout/stderr paths, receipt hash, full-CLI hash, source
revision, and fixture hash. Before input, validate receipt PID/executable/hash
identity and require exactly one AX window titled
`Simple registration regression` for that PID.

The PID-scoped observer must use AX coordinates in points, independent of
display pixel scaling. Read position `(x,y)` and size `(w,h)`, activate that
exact process, and use a titlebar point clear of the traffic lights (for
example `(x+100,y+7)` when inside its recorded bounds). Record a CGEvent drag
from that point to `(x+250,y+87)`, then require AX position `(x+150,y+80)`.
Click inside the new content bounds, send Q, and click the center of the
identified native AX close button using CGEvent coordinates. Revalidate the
same PID/window immediately before injection. Preserve each action and both
bounds; require the fixture assertions and natural PID/window disappearance.
AX `set position`, process-name selection, synthetic renderer events, or
forced process termination cannot substitute for these checks.

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

### Reconstructed checkout and monitoring readiness

The isolated checkout was reconstructed from preserved branch
`test/macos-winit-registration-close-20260922` at `d98cb8fdc85` under
`/Users/ormastes/simple-tmp/mac-winit-registration-20260922`. Its initial
worktree status was clean. `cliclick` resolves to `/opt/homebrew/bin/cliclick`
and `osascript` to `/usr/bin/osascript`. This establishes installed observer
tools only; AX permission and actual input delivery remain unverified.
No GUI application was launched during this audit. The live P0 Stage 2 build
owns bootstrap activity; this lane must wait for its admitted full CLI and
root-bound trusted GUI manifest. The existing assertions are unchanged.

The canonical launcher uses `open -n`, so LaunchServices starts the GUI
application outside the launcher's ordinary descendant tree. Wrapping only
`macos-gui-run.shs` in a process-tree RSS guard does **not** measure or contain
the application. Its strict PID receipt is written after the AX-window wait,
so a sampler started from that receipt also misses application startup.

Existing GUI evidence owners are
`scripts/check/check-macos-vulkan-web-live-evidence.shs` and
`scripts/check/check-macos-vulkan-gui-widget-live-evidence.shs`. They validate
receipt-selected executable paths and hashes and perform PID-specific cleanup,
but their RSS probes measure only the application PID after launch. The web
owner's `sample_peak_rss` also permits an absent sample. Neither is complete
startup-to-exit process-tree peak evidence. The accepted P0 checkout's
`scripts/resource/process-tree-rss-watchdog.pl` accepts a command to launch,
not an existing GUI PID; its documentation explicitly limits containment to
observed descendants/groups and reports `hard_memory_limit=0`.

Before the live run, arrange monitoring through the existing GUI evidence
owner, bound to the receipt's PID, process start identity, canonical executable,
and hash. Record sampled aggregate descendant RSS, CPU, sampling gaps,
launch-to-window time, and natural close-to-exit time. Reject missing or
malformed measurements and identity drift. Keep the cap at 5,859,375 KiB;
failure cleanup may signal only freshly revalidated owned identities and
must never count as successful native close. Post-receipt sampling alone must
be labelled as such, with startup and hard containment still unproven. An
earlier launch identity plus a monitor acknowledgment before workload startup
would be needed to remove the startup gap; no broad monitor was added here.

This is a readiness audit, not a test pass, performance comparison, memory
containment proof, or bug closure. The required live drag (+150,+80), content
click, Q, native close, and post-close assertions remain pending.

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
