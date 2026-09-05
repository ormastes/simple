# SimpleOS combined-server listener ownership leak

Status: fixed in working tree; static review pending; runtime verification not
run by instruction.

## Defect

The filesystem-launched combined server returned from `bind_listener` without
closing the socket when bind or listen failed. It also leaked a successfully
published HTTP listener when the database listener subsequently failed to
bind. Repeated failed service starts could therefore consume the process file
descriptor budget.

## Resolution

`src/os/apps/servers_user/main.spl` now keeps socket ownership local across
each fallible bind/listen transition and closes the exact descriptor before an
error return. Paired startup closes the HTTP listener when database listener
publication fails. Successful startup and normal shutdown are unchanged.

Focused coverage is in
`test/01_unit/os/apps/servers_user/listener_ownership_spec.spl`; architecture
and ownership rationale are in
`doc/05_design/os/server/listener_ownership_cleanup_v1.md`.
