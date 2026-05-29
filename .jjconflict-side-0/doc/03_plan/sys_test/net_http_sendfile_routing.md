# FR-NET-0003 System Test Plan — HTTP Static-File Sendfile Routing

System spec: `test/system/net_http_sendfile_routing_spec.spl`

Coverage:

- Portable worker capability summary is recorded as `portable-socket:portable`.
- Sendfile-capable backend summary is recorded as `sendfile`.
- Ordinary in-memory responses stay on the body send path.
- Static file responses use `portable-read` when sendfile is unavailable.
- Static file responses use `sendfile` only when `supports_sendfile` is true.
- A backend with `supports_zero_copy` but no `supports_sendfile` does not route to `submit_sendfile`, because this code path only has a file-to-socket sendfile operation.
