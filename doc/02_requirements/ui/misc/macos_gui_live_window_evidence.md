# macOS GUI Live Window Evidence Feature Request

## Status

Proposed. Deferred from the current Linux-host GUI hardening plan.

## Problem

Live macOS GUI visual acceptance cannot be proven from the current Linux
workspace. Existing macOS SMF/dynlib checks validate artifact identity and
hot-call transcript behavior, but they do not launch a visible macOS window,
capture pixels, or prove compositor/window visibility.

## Requested Feature

Add a macOS-host-only evidence lane that launches the Simple GUI macOS app,
captures the visible window, and emits deterministic visual evidence.

## Required Evidence

- Platform gate: pass only on macOS, fail closed elsewhere with
  `reason=requires-macos`.
- App launch evidence through the existing macOS GUI runner.
- Window detection evidence.
- Captured image artifact path.
- Capture byte count and checksum.
- Non-background pixel count or equivalent visible-content proof.
- Clear release-gate status that distinguishes live macOS visual proof from
  SMF/dynlib hot-call transcript proof.

## Candidate Files

- `scripts/check/check-macos-gui-live-window-evidence.shs`
- `test/03_system/gui/macos_gui_live_window_evidence_spec.spl`
- `doc/06_spec/system/gui/macos_gui_live_window_evidence_spec.md`

## Deferral Rationale

This requires a macOS host with GUI/screenshot access. It should not remain a
blocking item in the current Linux-host GUI hardening plan.
