# SimpleOS SOSIX positioned I/O: live route to release evidence

Status: implementation plan; not an installed service or release claim. This
advances RU-070 and V28 in the SOSIX unification design. Final SOSIX feature
and NFR requirements still require user selection.

## Source-backed starting state

- `src/os/kernel/abi/syscall_shim_positioned.spl` exports C leaves for
  syscalls 134/135 and retains a state value. `shim_init` resets it to
  uninstalled. No production caller invokes `shim_positioned_install_owner_v1`.
- Boot chooses the typed NVFS, DBFS, or FAT32 backend route, but
  `sosix_positioned_acceptance_round_trip_v1` owns a separate local registry
  with fixed process, capability, buffer, and operation identities. Its success
  proves backend composition only.
- `registry_lifecycle_v1.spl` and `service_buffer_registry_v1.spl` provide
  bounded transitions once authenticated facts and kernel-issued identities
  exist. `positioned_syscall_provider_v1.spl` requires exactly one capability
  and one registered buffer owned by the trap caller.
- The VFS IPC service's received wire header contains a source **port**, not
  an authenticated sender task ID. The kernel queue and typed receive result
  now retain `Scheduler.get_current()` only for trap-originated copied sends;
  direct manager sends and legacy metadata carry no provenance. The user IPC
  wire still does not carry that identity to `VfsService`. The current VFS IPC
  fd is also not a MountTable positioned file-object ID. Do not derive
  positioned authority from either number.
- `VfsService` now has source wiring for bounded syscall 133 reception and
  selects a 132 reply only for an `Async` request that minted a reverse-port
  permit. The PID1 catalogue entry point now exists and rejects zero-flag
  legacy requests before filesystem effects; its filter excludes syscall 20.
  The inline boot service still accepts tagged syscall 20 replies for its
  legacy caller bridge. `os.userlib.fs` and kernel `fd_io` now share one
  132/133 client transport; the latter retains the numeric VFS status needed
  by POSIX callers. This source route is compatible with the catalogue filter
  but has no admitted guest round trip or response-latency evidence.
  The updated wire specs remain unexecuted without an admitted Simple binary.
- The kernel copied-receive status/header/payload/provenance has one canonical
  `OwnedIpcReceiveResult` type in `ipc_types.spl`, replacing the syscall's
  local `any` view. The 32-byte user wire is unchanged, and the positioned
  control route remains uninstalled.
- The existing syscall IDs occupy 132/133 (owned IPC), 134/135 (positioned
  reads/writes), and 136/137 (PID1 root-service controls). `SyscallId` now
  names those six existing IDs; none is available for positioned control.
  The live x86_64 `rt_syscall_dispatch` switch in
  `examples/09_embedded/simple_os/arch/x86_64/boot/baremetal_stubs.c` handles
  134/135. A new control trap must be registered in that live switch and its
  C-ABI shim, not only in the Simple `syscall_handler` compatibility path.
- The owned IPC user library calls 132/133. The x86_64 dispatcher now routes
  those IDs to strong Simple handlers with bounded user copy and an
  owner-checked, non-consuming receive preview. The queue mints and consumes
  exact-pair reply permits. This is source wiring, not yet guest evidence;
  the trap and copyout behavior still need an admitted build and ring-3 test.
- The live x86_64 22/23 shims now retain the IPC manager state and use the
  scheduler caller. Their leaves validate name copy-in and require exact
  `IpcListen(name)` or `IpcConnect(name)` authority. Anonymous reply-port
  creation remains available without a named listen grant. The source change
  still needs ring-3 allow/deny and bad-pointer evidence.
- `root_service_catalog.spl` calls 136/137. The live x86_64 dispatch switch
  now reaches strong Simple catalog shims for both IDs. They adopt returned
  scheduler/IPC state; ring-3 PID1 service lifecycle evidence is still needed.
- The x86_64 network C switch reaches Simple shims for 70–77. Those shims now
  use the portable socket owner for exact socket-create, bind, listener, and
  accepted-connection checks; 77 checks `NetRaw`. [ARM64's direct endpoint
  authority gap](../../08_tracking/bug/simpleos_arm64_direct_socket_authority_2026-09-27.md)
  and RV64 network dispatch still lack this parity. No guest denial
  or successful network request has been admitted for the changed x86 route.

## Live syscall ingress and copied IPC prerequisite

| ID | User request | Live x86_64 route at this revision | Release action |
|---|---|---|---|
| 22/23 | Create anonymous/named endpoint; resolve named endpoint | Strong Simple shims retain returned IPC state; leaves validate names and exact named capability | Test allowed anonymous creation, denied service-name squatting, denied cross-name discovery, and bad user pointers in ring 3. |
| 132 | `ipc_send_owned_v1` / `ipc_reply_owned_v1` | C case and strong Simple shim now reach bounded copy-in, scheduler-current source-port check, and an exact `IpcConnect` check for cross-task requests | Verify cap issuance and ring-3 send/reply behavior. |
| 133 | `ipc_recv_owned_v1_into` | C case and strong Simple shim now preview, copyout, then dequeue | Verify single-owner serialization and ring-3 receipt with a bad-output-pointer negative control. |
| 134/135 | Registered positioned read/write | C switch and strong Simple shim present | Install a real registry owner and issue real file/buffer identities before claiming guest behavior. |
| 136/137 | PID1 root-service spawn/stop | C switch and strong Simple shims route to the catalog's scheduler-authenticated PID1 authority | Test a real ring-3 service lifecycle and denied non-PID1 call. |

`IpcManager.next_owned_payload_len` and `peek_owned` preserve the FIFO head
while the 133 handler checks and writes the bounded user output. The handler
then dequeues under the current single-core owner assumption; multi-core
delivery needs a serialized transition before release. The 132/133 handlers,
header encoder, endpoint inspection, and reply-permit methods now exist, but
their tests have not executed on an admitted self-hosted binary. Direct
`IpcManager.send_owned` calls still accept a caller-supplied `TaskId`; only
the trap shim derives it from `Scheduler.get_current()`. Do not use copied IPC
for positioned control until the guest path and its denial cases pass.
The cross-task request check requires a named `IpcConnect` grant. The finite
`CapabilityManager.mint_task_capability_set` issuer now builds a pledged pouch
with fresh identities and publishes it through the existing scheduler-pouch
check. Unit scenarios cover exact-name admission and identity freshness;
the issuer and its ring-3 service request still need admitted execution.

## Sender provenance ABI decision (unselected)

The kernel queue now keeps the sender `TaskId` that the trap's scheduler
reported. `IpcMessage.src_port` remains a port number, so a user service must
receive the task identity through a kernel-written field before it can use
that identity for positioned control. The choice below is pending user
selection; neither route is implemented or approved for release.

| Option | User contract | Pros | Cons | Effort |
|---|---|---|---|---|
| A: new copied receive version | Allocate a reviewed syscall ID after 137. Return a 40-byte fixed header: the existing 32-byte header, then the authenticated sender task ID as little-endian `u64`, then the payload. Keep 133 byte-for-byte unchanged. | One bounded copyout and an explicit version boundary; old services retain their exact ABI. | Requires live dispatch and shims on each supported architecture plus a new userlib decoder; mixed service versions need explicit routing. | High: about 3–5 implementation and guest-verification days. |
| B: opt-in v1 sidecar | Keep syscall 133 and its 32-byte record. Use its reserved `arg3` as an 8-byte sender-ID output pointer and `arg4` as an exact size/version flag; zero/zero retains current behavior. | Reuses the live dispatcher and current record decoder; smaller service migration. | Two user copyouts can leave partial output on failure; the opt-in flag makes the existing v1 contract more complex. | Medium: about 2–4 implementation and guest-verification days. |

Either option must reject a copied record lacking scheduler provenance,
authorize the receive endpoint against the current task, and leave the FIFO
head in place if any output validation or copy fails. The implementation must
test a nonzero sender ID, a forged source port, a wrong receiver, a bad output
pointer, replayed delivery, and the existing v1 32-byte fixture. It must also
show the task identity reaches `VfsService` without treating the source port
or VFS fd as file authority. The existing single-core peek/copy/dequeue
assumption needs a serialized transition before multicore release.

### VFS transport transition required for either ABI option

1. `VfsService` now calls bounded syscall 133 with a fixed receive arena and
   yields in its dedicated loop. The kernel's tagged syscall 20 enqueues
   copied payloads, so the existing client request frame can enter this path.
   Its header flags are zero and mint no owned reply permit; only the inline
   boot service retains that legacy reply route. The PID1 catalogue service
   rejects it, while both modes select a checked 132 reply for `Async` input.
   Verify both service modes in an admitted guest before promotion.
2. `vfs_ipc_request_bytes` now calls 132 with its caller-owned reply port and
   separate method word. A 132 request carries `Async` and mints the exact
   reverse-port permit. The service chooses the checked 132 reply from that
   flag; the client receives and validates the 133 header and frame length.
   It yields on EAGAIN to preserve its synchronous caller API. Admit this
   round trip and the kernel `fd_io` shared transport in a guest before promotion.
   Measure wait-loop yield count, response latency, and CPU service time under
   a delayed or failed VFS service; replace the polling wait with an admitted
   blocking notification or receive transition if it misses the selected NFR.
3. The source contracts now reflect both routes. Add executable inline-legacy /
   inline-service and owned-client / catalogue-service round trips, malformed lengths,
   wrong receiver, missing reply permit, and EAGAIN handling. The 133 path is
   nonblocking, so the dedicated service loop yields rather than spins.
   Verify kernel `fd_io._vfs_ipc_request` preserves numeric VFS status and
   transport-failure cleanup through the shared 132/133 route.
4. Only after the copied transport is live should the selected provenance
   ABI feed a task identity to positioned control. Neither the source port nor
   the VFS fd may stand in for that identity.

## Contract and owner placement

1. Keep the registry and request-token state beside the existing
   `g_shim_positioned_state`. A kernel-owned control function may publish a
   replacement state only after the matching registry transition accepts.
   Calls that fail must retain the prior state. The shim's 134/135 leaves keep
   using `g_shim_scheduler.get_current()` for caller identity.
2. Install the owner after the real filesystem backend and service endpoint
   are live. Endpoint and generation must come from the owning kernel/service
   lifecycle, not from the test route or an arbitrary caller value. Installation
   may start with an empty registry, but boot must still report user positioned
   I/O unavailable until the first real capability and buffer are admitted.
3. Add control requests at the kernel trap boundary, where the scheduler's
   current task is authenticated. Allocate any new syscall numbers through the
   canonical syscall registry and review their ABI before implementation.
   Do not add a VFS IPC control method until its delivery path supplies an
   authenticated sender identity retained across queueing and reception.
4. The kernel opens a positioned VFS file object under the caller's file
   policy, issues a fresh capability slot/generation, and registers only the
   rights granted by the open. The returned handle is an opaque capability
   reference. The caller cannot submit a raw file-object ID as authority.
5. Buffer registration copies a bounded user byte range into service-owned
   storage, issues a fresh slot/generation and registration ID, and returns a
   receipt. Reads update the owned copy; a separate authenticated fetch copies
   the result back to the caller. Never retain a user pointer after the
   registration trap. All byte copies use the existing kernel user-memory
   validation/copy boundary, with overflow and maximum-size checks before
   allocation or effect.
6. Existing 134/135 envelopes resolve the opaque capability to one file
   object for the authenticated caller, then resolve one owned buffer receipt
   and execute the canonical service transaction. The dispatcher must not
   emulate positioned I/O with seek/read/write/restore. Failed authorization,
   range, or backend checks leave the request token and buffer unchanged.
7. Close, buffer unregister, process exit, service restart, unmount, and
   backend replacement retire the matching entries and wait for or quarantine
   in-flight operations before releasing file objects or owned bytes. Exhausted
   generations and request tokens stay tombstoned (see PR #1688); an old
   receipt never regains validity. Multiple cores require a serialized owner
   transition, rather than unsynchronized writes to the shim globals.

## Implementation order

| Step | Source owner | Required exit evidence |
|---|---|---|
| 1. Freeze control ABI and identity issuer | canonical syscall registry, `src/os/sosix/fs/` | no ID collision; malformed, stale, cross-process, and exhaustion cases specified |
| 2. Kernel control transitions | `src/os/kernel/abi/`, registry and buffer owners | authenticated scheduler caller; one state publication per accepted transition; rejected transitions preserve state |
| 3. Boot and lifecycle wiring | `src/os/kernel/boot/`, VFS mount/service lifecycle | real endpoint/generation and typed backend installed; restart/unmount removes stale authority |
| 4. Caller API | `src/os/userlib/` | open/register/pwrite/pread/fetch/retire use only returned opaque identities and bounded copies |
| 5. Guest execution | `test/03_system/os/qemu/` | real user task enters both 134/135 C-ABI leaves; file offset and fetched bytes checked independently |
| 6. Release verification | SOSIX V05/V12/V28, SimpleOS release ledger | capability, trap, service, driver, retirement, and failure evidence from guest; all required gates PASS |

Keep the legacy VFS IPC service and the local backend route as separate
compatibility/oracle paths until the guest route passes. The control ABI and
ownership transition are the immediate implementation dependencies; a boot
call that installs a fabricated registry would not satisfy the gate.

## Minimum executable matrix

- Valid process: open a real mounted file, register a four-byte owned buffer,
  write two bytes at nonzero offset, read four bytes at offset zero, fetch the
  owned result, and compare both file bytes and unchanged cursor. Observe
  actual trap entry and selected backend identity in the guest.
- Denials: no owner, no capability, missing read/write right, wrong process,
  wrong buffer slot/generation/registration ID, range overflow, stale file,
  stale endpoint, and duplicate identity. Every denial leaves file bytes,
  registry bytes, cursor, and request token unchanged.
- Lifetime: retire during outstanding work, process exit, unmount/remount,
  service generation change, token/generation exhaustion, and backend loss.
  Delayed completion cannot write into a new owner generation.
- Resource/performance: 64-buffer and capability-table bounds, owned-byte
  budget, no unbounded trap allocation, and measured guest startup, positioned
  request latency, and maximum RSS against selected NFRs.

Passing existing unit seams or the boot local round trip does not replace the
guest V28 test. The route remains unavailable for release until that test and
its negative controls execute on an admitted self-hosted toolchain.
