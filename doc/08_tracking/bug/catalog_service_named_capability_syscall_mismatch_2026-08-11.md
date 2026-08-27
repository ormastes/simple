# Catalogue service capabilities do not match live syscall requirements

**Status:** Partially resolved — named IPC is live; endpoint generations and
network route authority remain open

## Evidence

`src/os/kernel/loader/root_service_catalog.spl` correctly mints exact named
authority for its service children, for example `IpcListen("vfs")`,
`IpcConnect("net")`, and `NetListen(80)`.

The original generic syscall dispatcher checked IPC operations with
`IpcListen("")` / `IpcConnect("")`; a child holding `IpcListen("vfs")` could
not pass, and an implementation that loosened the check would have created a
wildcard endpoint bypass.

As of the 2026-08-11 critical-path implementation, syscall IDs 20–23 and
132–133 resolve the actual endpoint name from the live port table and check
that exact typed capability. Creation/connect copy and validate a user name
once, so the authorization and operation use the same bytes. Receive also
requires live ownership. The bound copied-payload path mints a bounded,
one-shot reply permit only after a request has been copied successfully; it is
consumed after the matching reply and removed on task exit. This makes replies
possible without granting a service wildcard access to all client endpoints.

Do **not** solve this by adding wildcard IPC or port-zero capabilities to the
catalogue. That would erase the named least-authority policy and create an
ambient endpoint-access bypass.

## Required resolution

1. Replace numeric endpoint IDs with typed endpoint handles carrying a
   generation and connect/listen rights; the current monotonic IDs avoid reuse
   but are not yet first-class CSpace handles.
2. Make bind/connect authorize their actual port/route; `listen` and `accept`
   must operate only on a socket previously bound under that authority.
3. Add live scheduler tests proving `vfs` cannot connect to `net`, HTTP cannot
   bind another port, and no named capability authorizes an unrelated endpoint.

This is independent of the missing service payload/driver broker work. It must
be resolved before any catalogue service can be accepted as capability-confined.
