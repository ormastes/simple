# MinIO GET reports a truncated body as success

Status: fixed 2026-10-31, found by the emulated specs.

When a server closes the socket before `Content-Length` bytes arrive,
`minio_get_object` (`src/app/devhub/adapter_minio.spl:457`) returns `ok=true` after one
request, so no retry fired. `rt_http_request` reported no transport error and a 2xx
status. A caller cannot tell a damaged object from a good one. Curl-based adapters report
the same condition as an error (curl exit 18), so this is specific to the
`rt_http_request` path.

## Reproduction

`test/03_system/app/devhub/feature/devhub_minio_emulated_spec.spl`, scenario "reports a
truncated body as an error". Observed: `expected true to equal false`, and one `REQ` line
in the emulator log where three are scripted. The spec failed until the fix below.

## Fix

`minio_get_object` now uses `_minio_get_checked`: `http_request_v2_raw` exposes the raw headers, so a `Content-Length` differing from the bytes received is a transport error and retries. If v2 is unavailable on Windows it falls back to curl, which reports a short body itself. No seed rebuild was needed. `into_string().unwrap_or_default()` in `rt_http_request` remains, and other callers of that extern (`_signed_get` listings, HEAD) keep the old behaviour; the listing closing-tag check covers listings.
