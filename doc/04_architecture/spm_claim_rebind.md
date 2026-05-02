# SPM Claim Rebind Architecture

Feature: FR-SPM-0003.

## Flow

1. Kernel boot registers `SPM_PORT_WELL_KNOWN_TASK_ID`.
2. The SimpleOS SPM process starts and calls `sys_spm_claim()`.
3. `syscall_handler` routes id 115 to the SPM claim handler with `caller.id`.
4. The handler checks the caller privilege mirror against
   `id.system.spm.claim`.
5. `spm_port_claim` rebinds the placeholder to the caller, accepts same-task
   retries, and rejects a second real owner.

## Boundary

`spm_port.spl` owns port state and rebind mechanics. `spm_claim.spl` owns the
privilege-mirror gate and claim decision. `syscall.spl` owns caller identity
and dispatch. `syscall_raw.spl` exposes the userland wrapper.
