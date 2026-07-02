# Bug: check-simpleos-wm-qmp-drag-delta-evidence.shs invokes a nonexistent entry file

- **Date:** 2026-07-02
- **Severity:** medium (gate cannot run at all)
- **Area:** scripts/check/check-simpleos-wm-qmp-drag-delta-evidence.shs

## Symptom
The gate runs `bin/simple run simpleos_desktop_qmp_launch_root.spl`, but no file
with that name exists anywhere in the repo, so the gate fails unconditionally.
Reproduced on macOS host 2026-07-02, independent of any local changes.

## Expected
The gate should invoke the actual QMP launch entry (see
`src/app/test/simpleos_desktop_qmp_launch.spl` and the
`_wm_simple_web_qmp_capture_target()` flow) or the missing root wrapper should
be restored. Likely a casualty of an entry-file rename/move.
