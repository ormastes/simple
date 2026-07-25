# Theme rendering and WM host/simpleOS sync state (2026-07-25)

## Current code changes in progress
- Fixed WM/theme IDs to use active WM theme snapshots (with default fallback) instead of hardcoded `dark` / `aetheric_dark` in:
  - `src/app/ui.web/wm_bridge.spl`
  - `src/app/ui.web/_HostTaskbarRuntime/mode_and_layout_helpers.spl`
  - `src/app/ui.web/server.spl`
  - `src/app/ui.web/html.spl`
  - `src/os/compositor/wm_action_applier.spl`
  - `src/os/compositor/simple_gui_window_renderer.spl`
  - `src/os/compositor/host_wm_theme_bootstrap.spl`
  - `src/os/compositor/simpleos_wm_theme_bootstrap.spl`
- Theme fallback strategy now:
  - prefer active WM chrome snapshot if present;
  - else apply and use default package snapshot;
  - else fallback to existing aetheric-generated snapshot.

## Parallel agent findings (host + QEMU)
- `check-hosted-wm-capture-evidence.shs`: PASS.
  - Evidence in `build/hosted-wm-capture-evidence/*` and
    `doc/09_report/hosted_wm_capture_evidence_2026-07-25.md`.
  - Noted backend: simple Web raster local readback path currently used; Metal GPU path not fully wired.
- `check-simpleos-x86-64-wm-qemu-preflight.shs`: PASS.
- `check-simpleos-x86-64-wm-qemu-readiness.shs`: FAIL here (`grub-mkstandalone` missing), so QEMU boot path blocked.
- `check-simpleos-arm64-wm-qemu-readiness.shs`: PASS.
- `check-simpleos-wm-visible-display-evidence.shs`: FAIL here for same grub tooling blocker.
- `doc/09_report/simpleos_wm_visible_display_evidence_2026-07-25.md` added by validation run.

## Sync/push plan
- Check sync with current remote (fetch + rebase) before commit.
- Commit current state with focused message.
- Push to `main@origin` bookmark flow per repository workflow.
