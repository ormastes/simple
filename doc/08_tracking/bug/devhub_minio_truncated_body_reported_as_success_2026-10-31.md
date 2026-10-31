# MinIO GET reports a truncated body as success

Status: open. Found 2026-10-31 by the emulated MinIO spec on the Windows Phase 1 seed.

When a server closes the socket before `Content-Length` bytes arrive,
`minio_get_object` (`src/app/devhub/adapter_minio.spl:457`) returns `ok=true` after one
request, so no retry fired. `rt_http_request` reported no transport error and a 2xx
status. A caller cannot tell a damaged object from a good one. Curl-based adapters report
the same condition as an error (curl exit 18), so this is specific to the
`rt_http_request` path.

## Reproduction

`test/03_system/app/devhub/feature/devhub_minio_emulated_spec.spl`, scenario "reports a
truncated body as an error". Observed: `expected true to equal false`, and one `REQ` line
in the emulator log where three are scripted. The spec stays RED.

## Unblock

Root cause: `response.into_string().unwrap_or_default()` at `:141` and `:150` turns a
read error into an empty body (`:61` has the same shape). Return it as a transport error
instead. The extern lives in the
seed (`src/compiler_rust/compiler/src/interpreter_extern/network/mod.rs:88`), and native
callers use their own runtime path, so a fix needs a seed rebuild and a check of both.
The adapter cannot detect this alone: the extern exposes no response headers
(`adapter_minio.spl:577`). The native path was not tested here.
