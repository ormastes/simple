# Bitbucket 5xx errors dropped the HTTP status from the message

Status: fixed 2026-10-31. Found by the emulated gh parity spec.

`bb_map_http_error` (`src/app/devhub/adapter_bitbucket_protocol.spl:310`) used the raw
response body as the whole message for any status it did not name. A 500 with body
`server exploded` printed `error: server exploded`, with nothing saying it was a server
failure, while GitHub through `gh` printed `HTTP 500`.

The fix prefixes `api_error (HTTP <status>): `, the same wording as `_bbc_status_label`
in `adapter_bitbucket_curl.spl`.

Specs in `test/03_system/app/devhub/feature/devhub_gh_parity_emulated_spec.spl`:

- Reproduction: "reports an error for a 500 on bitbucket".
- Generalisation: "names the status of a 503 on bitbucket".
