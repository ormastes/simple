# SPM Claim Rebind System Test Plan

Feature: FR-SPM-0003.

## SPipe

`test/system/spm_claim_rebind_spec.spl`

## Coverage

- Deny without claim privilege.
- Authorize `id.system` mirror for `id.system.spm.claim`.
- Rebind boot placeholder to real SPM task.
- Same-task claim is idempotent.
- Second real task is rejected.
- `SysSpmClaim` is id 115.
