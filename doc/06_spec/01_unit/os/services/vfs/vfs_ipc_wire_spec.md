# VFS copied IPC wire contract

## Purpose and scope

This manual describes the 12 source-contract scenarios in
`test/01_unit/os/services/vfs/vfs_ipc_wire_spec.spl`. They guard the named VFS
endpoint, bounded request and reply frames, shared user and kernel client
transport, POSIX flag values, and VFS handle retirement. The companion
`doc/03_plan/os/simpleos_sosix_positioned_live_route_2026-09-27.md` records
the guest evidence still required for release.

## Operator workflow

Run the executable spec with the admitted self-hosted Simple test runner:

```text
bin/simple test test/01_unit/os/services/vfs/vfs_ipc_wire_spec.spl
```

Read each scenario verdict. A failed source assertion identifies a changed
wire assumption that must be checked against the actual kernel, service, and
client behavior before the assertion is updated.

## Wire and ownership

- Clients create an anonymous reply port and connect to the named `vfs` port.
- `ipc_send_owned_v1` sends the method and bounded payload through syscall 132.
  The service receives a copied v1 record through syscall 133.
- The catalogue service accepts owned `Async` requests; the inline boot
  service also accepts legacy zero-flag requests. Replies use the matching
  route. The owned client validates the reply endpoints, flags, frame length,
  and numeric VFS status.
- `src/os/kernel/fd_io.spl` uses the same userlib transport and preserves the
  numeric status separately from transport failure.
- Userlib destroys its temporary reply port on every terminal request path.
  On live x86, syscall 18 reaches the Simple owner check and retains its
  updated IPC state. A foreign task cannot destroy that port.

## Scenario map

| Scenario | Contract checked |
|---|---|
| Named VFS service and reply bounds | Named registration, copied receive, bounded reply storage |
| Canonical request shapes | Method-specific payload lengths and path delimiters |
| POSIX OPEN layout | Access, create, append, and truncate bit decoding |
| Shared fd_io transport | One 132/133 client with numeric status preservation |
| File data and cursor | Bounded handle frames and positioned read/write cursor rules |
| Reply-port owner shim | Userlib cleanup, strong Simple handler, live x86 dispatch |
| Final-alias close | Remote close only for the final local FD alias |
| Close receipts | Bounded issued-handle retirement and unknown-handle rejection |
| User VFS facades | Shared copied ABI and mount-list method IDs |
| User OPEN producers | Frozen POSIX flag values |
| Anonymous reply ports | Cleanup and handle-based file frames |
| READDIR text | Opaque name after the first wire delimiter |

## Evidence limits and recovery

These scenarios inspect source text. They detect drift in selected symbols and
call sites; they do not prove a booted guest, successful IPC exchange, security
behavior, or performance. Release requires executable inline and catalogue
round trips, malformed-frame and wrong-owner controls, repeated requests with
port retirement, and guest measurements from the linked plan. No runtime PASS
is claimed by this manual.
