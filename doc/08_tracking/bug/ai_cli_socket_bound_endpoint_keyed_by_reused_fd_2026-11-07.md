# AI-CLI socket endpoint grant keyed by a reusable fd number (2026-11-07)

Status: fixed (2026-11-14, `work/aicli-socket-endpoint-open-file-20261114`).
Pre-existing on release/1.0.0; found in review of
`work/arm64-el0-net-ipc-20261107`.

`g_ai_cli_socket_bound_fds` / `g_ai_cli_socket_bound_endpoints`
(`src/os/kernel/socket_compat.spl`, ~lines 41-42) record a bound endpoint
per fd NUMBER at bind (~:144) and read it at listen (~:153) into
`_socket_grant_errno("listen", ...)`. Nothing clears them on `fd_close`,
`fd_dup2`, close-on-exec or process exit, so a reused fd number carries a
stale endpoint into the AI-CLI manifest decision.

This is the same defect class the branch fixed for the capability ports by
moving them onto the fd table's open-file object (`of_net_bound_ports`,
`src/os/kernel/fd_table.spl`, reset on last-reference release). Fix: store
the endpoint the same way, or key by `fd_get_object_id(fd)`; pin with a
reuse-after-raw-close case like `socket_port_provenance_spec`.

## Fix (2026-11-14)

Confirmed live on origin/release/1.0.0 `bc9b18b3106`
(`socket_compat.spl:41-42` side table, `:351-366` record/lookup by fd number).

The endpoint now lives on the open-file description exactly like the #7480
ports: `of_net_bound_endpoints: [text; 256]` in `src/os/kernel/fd_table.spl`,
reset to `""` in `fd_table_init`, the last-reference branch of
`_fd_release_object_ref`, and `fd_set`; accessors
`fd_set_net_bound_endpoint` / `fd_get_net_bound_endpoint`. `dup` shares it;
`fd_close`, `fd_set` over a slot, `dup2`, close-on-exec and process exit all
release it. The `g_ai_cli_socket_bound_*` globals and their re-export from
`src/os/posix/socket_compat.spl` are deleted. Lockless: plain arrays, single
kernel owner, same assumption as the rest of the fd table.

Evidence (seed runner, host): `test/01_unit/os/kernel/socket_endpoint_provenance_spec.spl`
red before the fix (6 executed, 1 passed, 5 failed: raw-close reuse, fd_set
overwrite, dup2, dup share, posix_close_socket) -> green 6/6 after.
Regression: socket_port_provenance_spec 7/7, generic_syscall_net_portable_route_spec 5/5,
portable_net_shim_capability_spec 3/3, posix socket_compat_spec 8/8.
