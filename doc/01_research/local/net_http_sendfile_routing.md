# FR-NET-0003 Local Research — HTTP Static-File Sendfile Routing

Status: implemented research note.

Relevant code:

- `src/lib/nogc_async_mut/io/driver.spl` exposes `IoDriver.net_capabilities()`, `supports_sendfile()`, and `submit_sendfile()`.
- `src/lib/nogc_async_mut/io/net_backend.spl` defines `NetBackendCapabilities`, portable capabilities, capability summaries, and `net_backend_static_file_route`.
- `src/lib/nogc_async_mut/http_server/static_file.spl` emits large static files as `HttpResponseData.body_file`.
- `src/lib/nogc_async_mut/http_server/worker.spl` stores `net_capabilities` and `net_backend_summary` at worker creation, converts unsupported `body_file` responses through `worker_static_file_fallback_response`, and chains `submit_sendfile` only after a header send completes on the `sendfile` route.

Conclusion: the implementation exists. The missing work was traceability and SSpec coverage proving sendfile is capability-gated, zero-copy-only backends do not take a nonexistent file-to-socket path, and portable backends keep the read-plus-send fallback.
