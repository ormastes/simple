# SimpleOS Desktop Core Formal Verification — System Test Plan

## Goal

Validate the research-first verification package with executable specs now, then define the next system-evidence gates for the later proof-bearing phase.

## Current Phase: Pure And Spec-Checked Gates

### Gate ST-1: Existing kernel seam remains green

- run `doc/06_spec/app/os/feature/rv64_user_mode_exec_spec.spl`
- expected:
  - pass
  - no regressions in trap/syscall/privilege seam behavior

### Gate ST-2: New combined OS-core verification spec passes

- run `doc/06_spec/app/os/feature/simpleos_desktop_core_formal_verification_spec.spl`
- expected:
  - pass
  - exercises both kernel-core and desktop-contract slices

## Next Phase: Proof-Bearing Readiness Gates

### Gate ST-3: Verification CLI works cleanly

- command:
  - `bin/simple verify status`
- expected:
  - no export-resolution/interpreter failure
  - usable artifact inventory and status output

### Gate ST-4: Desktop readiness markers remain deterministic

- target:
  - named desktop QEMU lane from `src/os/qemu_runner.spl`
- expected markers:
  - `boot`
  - `shell-ready`
  - `launcher-ready`
  - `desktop-ready`
  - `shortcut:ok`
  - `wm:ok`

### Gate ST-5: Claim audit

- docs and reports must use the evidence taxonomy correctly:
  - `proved`
  - `model-checked`
  - `spec-checked`
  - `system-tested`
  - `assumed`

## Exit Criteria

- both current pure/spec gates pass
- docs exist and are cross-linked
- no doc claims stronger assurance than the package supports
