# FR-NET-0003 Design — HTTP Static-File Sendfile Routing

Worker startup:

- `Worker.create` calls `driver.net_capabilities()`.
- The resulting `NetBackendCapabilities` and `net_backend_summary(caps)` are stored on the worker for request routing and observability.

Static file response model:

- `StaticFileHandler` returns in-memory bodies for small files.
- Large files are represented as `HttpResponseData.body_file`, `body_offset`, and `body_length`.

Routing:

- `net_backend_static_file_route` owns the pure capability decision.
- `worker_static_file_route` adapts `HttpResponseData.body_file` to that helper.
- The route is `body` for ordinary responses.
- The route is `sendfile` only when a file body is present and `caps.supports_sendfile` is true.
- The route is `portable-read` otherwise, including zero-copy-only backends, because this worker path has `submit_sendfile` but no separate file-backed zero-copy send API.

Execution:

- The portable route materializes the file into the response body before sending.
- The sendfile route sends headers first, opens the file, submits `driver.submit_sendfile`, closes the file descriptor on completion, and then advances the connection state.
