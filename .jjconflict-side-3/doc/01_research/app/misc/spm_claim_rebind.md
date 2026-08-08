# SPM Claim Rebind Local Research

Feature: FR-SPM-0003.

## Existing Code

- `src/os/kernel/ipc/spm_port.spl` owns the registered SPM task id and already
  rejects registration by a second distinct task.
- `src/os/kernel/boot/init_services.spl` registers the placeholder task id
  `0xfffffff0` during boot.
- `src/os/kernel/ipc/syscall.spl` dispatches SPM syscall ids 110-114 and now
  has caller task id available in the dispatcher.
- `src/os/userlib/syscall_raw.spl` contains user-facing wrappers for SPM
  syscall ids 110-114.
- `src/app/simple_process_manager/main.spl` chooses the SimpleOS transport at
  startup and is the right userland call site for claiming the port.

## Decision

Add `SysSpmClaim = 115`, gate it with the existing privilege mirror check for
`id.system.spm.claim`, allow rebind from the boot placeholder, and reject a
second real owner.
