# SPM Claim Rebind Design

Feature: FR-SPM-0003.

## Design

- Add `SPM_PORT_WELL_KNOWN_TASK_ID` and `spm_port_claim(task_id)` to the port
  module.
- Add `SysSpmClaim = 115` to the syscall id enum.
- Add `spm_claim_authorized(task_id)` and `spm_claim_for_task(task_id)` in a
  small IPC policy module for direct SPipe coverage and syscall reuse.
- Add `sys_spm_claim()` to raw userland syscall wrappers.
- Call `sys_spm_claim()` when SPM selects the `simpleos` transport; fail startup
  if claim is denied.
