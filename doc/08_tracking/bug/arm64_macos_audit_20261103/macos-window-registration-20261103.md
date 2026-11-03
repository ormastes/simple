# Single-bug qualification: macOS window registration

Bug: `gui_winit_window_not_registered_window_server_2026-07-06`.
Assigned claim session: `macos-window-20261103` (parent serializes claim/database).
Source: `d8d65cbe7da153c64c3ecc596f04a44bebb218c5` in `/tmp/simple-arm64-macos-bug-db-20261103`; host `Linux aarch64`.

## Current source and meaningful checks

The real creation path is intact: `src/runtime/spl_winit/src/lib.rs:239` creates the window through the active event loop, and line 290 invokes `activate_frontmost`. The macOS implementation establishes Regular activation (446), activates the app (450), and orders its NSWindow key/front (459–460). Event-loop construction selects Regular and activate-ignoring-other-apps before windows are created (614–616). These are existing repairs, not edits by this agent.

The 59-line live SSpec `test/03_system/app/gui/feature/macos_window_registration_spec.spl` creates a real winit window and bounds polling to 60 seconds. It asserts presentation, moved/mouse/Q events followed by close, then asserts disposed operations fail. The companion manual correctly requires an independent PID-scoped AX bounds delta (+150,+80); an initial moved event alone cannot pass acceptance.

Executed once, without build or GUI launch:

1. `sh test/01_unit/scripts/macos_gui_run_pid_lookup_contract_test.shs`: exit 0, `CONTRACT=PASS`. It extracts actual launcher functions, finds PID 4242 despite a large ps tail, and its old early-exit negative control fails with SIGPIPE exit 141. Marker-free binaries are rejected without a dylib; dynamically available non-strict support is recognized; strict baked-symbol check refuses the marker-free candidate. Log: `macos-window-pid-contract.log`. This is portable launcher proof, not native window proof.
2. Source canonical execution-history helper and invoke `macos_gui_history_require_trust_root "$PWD"`: exit 125, explicitly “tracked policy keeps EndpointSecurity collector unavailable until source, reproducible provenance, team signing identity, and entitlement are admitted.” Log: `macos-window-trust-root.log`. This is current admission refusal, not a reproduced window failure.

## Exact unresolved acceptance

- Native macOS GUI host with authorized AX/CGEvent input and current `libspl_winit.dylib`.
- Admitted Endpoint Security collector: tracked policy currently has `status=unavailable`, `signing_identity=unassigned`, `team_identifier=unassigned`.
- Root-bound trusted current pure-Simple full-CLI GUI artifact/manifest. Neither canonical `build/bootstrap/full/aarch64-apple-darwin/provenance/gui-driver.env` nor `build/sffi/libspl_winit.dylib` exists in this worktree. Passing Stage2/3 CI alone does not supply GUI provenance.
- Strict launcher receipt proving selected/bundled/trusted hashes and exact window-owning PID match. Current launcher resolves PID at line 399, waits for AX ownership at 417, then publishes receipt at 427; post-receipt RSS sampling cannot claim startup coverage. Record startup/CPU/RSS sampling gaps honestly; existing manual already documents this limitation.
- On that exact PID: real titlebar drag (+150,+80), AX before/after bounds, content click, Q, native close, successful SSpec assertions, natural PID/window disappearance, and bounded resource evidence. Do not disable strict mode or substitute simulated renderer events.

No newly demonstrated current source defect justifies a production patch. No new source/spec edit, commit, PR, native run, or closure is claimed. Recommend retain open, or parent-reviewed transition to `fix-implemented-verification-pending` with the above required native check. The parent owns claim release/waiting event and canonical metadata.

## Source hashes

- Fixture SHA-256: `29e3cbfc33550f47d8332a0347e947ea79dbbe88c02b2a517a4b3f1ae18620bc`
- Launcher SHA-256: `7c33644b1640b9746009ef26692a0eac801dda524bbb1c33a9e6141aa0d5cc88`
- Winit provider source SHA-256: `2758ec09944f05f5f83715d2921553fe94651f2943cea34aa59e0c64d662d71f`
