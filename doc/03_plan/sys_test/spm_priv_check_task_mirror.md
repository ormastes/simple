# SPM Privilege Check Task Mirror System Test Plan

Feature: FR-SPM-0002.

## Coverage

- Caller whose mirror covers the requested id path is allowed.
- Caller with a different mirror is denied.
- Caller without a mirror is denied.
- Empty id path is denied.

## Spec

- `test/system/spm_priv_check_task_mirror_spec.spl`
