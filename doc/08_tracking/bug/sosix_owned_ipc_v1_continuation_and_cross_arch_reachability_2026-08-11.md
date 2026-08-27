# SOSIX Owned IPC v1 Continuation and Cross-Architecture Reachability

**Date:** 2026-08-11  
**Status:** OPEN  
**Requirements:** REQ-SQ-002, REQ-SQ-004, REQ-SQ-015

## Landed boundary

Additive syscall IDs 132/133 provide bounded owned-copy send and nonblocking
receive. Legacy metadata-only syscall 20/21 is unchanged. The kernel validates
the current task and claimed source endpoint, copies through checked VMM
helpers, and does not consume a receive message when capacity or destination
validation fails. The x86_64 ring-3 C dispatcher now reaches the strong Simple
shims.

## Remaining gaps

- A nonzero receive wait policy returns `ENOSYS`. The current trap API cannot
  retain an output pointer/capacity and resume copyout after scheduler wakeup.
  Compatibility waits must use notification plus repeated nonblocking receive
  until a continuation-safe syscall contract exists.
- ARM32, ARM64, RISC-V32, RISC-V64, and x86_32 acceptance kernels do not yet
  expose an equivalent ring-3 syscall dispatch path for 132/133. Do not infer
  cross-architecture transport reachability from the x86_64 C switch.
- The VFS service and user client have not migrated to the v1 envelope, service
  discovery, registered-buffer table, or dedicated reply endpoint.
- Production strong-shim paths still need an executable capability-enforcement
  proof; source-endpoint ownership alone is not destination authorization.

## Resume gates

1. Add a user client and VFS service adapter over the frozen v1 codec.
2. Prove a real owned-copy request/reply round trip with source authentication.
3. Implement notification-driven compatibility waiting without busy spin.
4. Add architecture dispatch/reachability for each guest only when that guest
   has a real user-mode syscall path.
5. Prove capability denial through the production dispatcher, then run one
   fresh QEMU transport round trip per applicable architecture.

No existing boot/list/program receipt proves these gates.
