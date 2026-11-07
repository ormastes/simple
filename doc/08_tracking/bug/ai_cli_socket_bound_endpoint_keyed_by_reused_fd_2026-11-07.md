# AI-CLI socket endpoint grant keyed by a reusable fd number (2026-11-07)

Status: open. Pre-existing on release/1.0.0; found in review of
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
