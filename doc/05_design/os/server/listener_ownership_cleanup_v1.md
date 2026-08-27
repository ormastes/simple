# SimpleOS combined-server listener ownership cleanup v1

## Scope

The filesystem-launched combined HTTP/database process preserves its existing
ports, protocols, APIs, and successful serve loop. This change only closes
kernel socket descriptors whose ownership would otherwise be lost during
startup failure.

## Ownership transitions

- `bind_listener` owns a socket immediately after `socket` succeeds.
- A bind or listen error closes that exact descriptor before returning `Err`.
- A listen success transfers the live `Socket` to the caller in `Ok`.
- During paired startup, a successful HTTP listener remains caller-owned until
  the database listener result is known. If database bind fails, the caller
  closes the HTTP descriptor before closing the database service and returning.
- The existing success path owns the HTTP listener through the bounded serve
  loop and closes it once during normal shutdown.

The cleanup decision is constant time and allocation-free. It adds no request
hot-path dispatch, buffer copy, or protocol behavior. The production branches
share pure ownership predicates with the focused behavioral spec, while the
actual close remains inside the socket owner.

## Evidence boundary

`test/01_unit/os/apps/servers_user/listener_ownership_spec.spl` exercises the
pure paired-startup decision and inspects both fallible socket-owner branches.
Live syscall and QEMU verification are intentionally outside this focused
change.
