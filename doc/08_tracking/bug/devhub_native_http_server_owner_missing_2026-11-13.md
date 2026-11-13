# devhub native link: seed-only HTTP server/WebSocket externs, and no SOSIX HTTP-client/TLS owner

- **Date:** 2026-11-13
- **Status:** OPEN (link blocker fixed by import narrowing; SOSIX gap open)
- **Severity:** Medium. Before the fix, the Phase 4 native build of `src/app/devhub/main.spl` failed at link time.
  The SOSIX gap leaves devhub's HTTP client outside the SOSIX host-access rule.
- **Area:** `src/lib/nogc_sync_mut/http_client/transport.spl`, `src/lib/nogc_sync_mut/sosix/network.spl`,
  `src/lib/nogc_sync_mut/io/http_client_core.spl`, `src/lib/nogc_sync_mut/io/http_sffi.spl`

## Symptom

A frozen Windows Phase 2 pure-Simple compiler, building with the LLVM backend from source `4b7375e435a`,
refused the devhub link:

```
extern fn rt_http_client_set_header is declared but not implemented anywhere -- declared at src/lib/nogc_sync_mut/io/http_sffi.spl:45
```

The same error appeared for `rt_http_upload`, `rt_http_server_{create,route,static,start,stop,destroy}` and
`rt_ws_{connect,send,receive,close}`, all declared in `io/http_sffi.spl`.

## Root cause

devhub uses none of these externs. They reached its closure through one import:
`std.http_client` -> `http_client/transport.spl` -> `use std.nogc_sync_mut.io.http_sffi.{http_request_raw}`.
`http_sffi` re-exports `http_request_raw` from `io.http_client_core` (`export use`), so the import pulled in
every legacy seed-only extern in `http_sffi` just to reach a function owned by `http_client_core`.
No other module in the 301-file devhub closure imports `io.http_sffi`.
The same class was fixed for duplicate-check in #8690/#8706.

## Fix (landed with this record)

`transport.spl` now imports `std.nogc_sync_mut.io.http_client_core.{http_request_raw}` directly.
The call target is the same function, so behavior does not change and no new `rt_*` owner is introduced.

## Open gap: SOSIX has TCP only

Owner rule (2026-11-13): all host access goes through SOSIX owners, except the startup path.
`src/lib/nogc_sync_mut/sosix/network.spl` exposes only `sosix_tcp_*`. SOSIX has none of the following:

| capability | SOSIX owner | devhub user today |
|---|---|---|
| HTTP client (request/response, headers, body, timeout) | none | `http_client` (`adapter_outlook.spl`), `io.http_client_core` `rt_http_request`/`rt_http_download`/`http_request_v2_raw` (`adapter_minio.spl`, `cmd_api.spl`) |
| TLS (HTTPS: GitHub, Jira, Confluence, Outlook/Graph, MinIO) | none | same as above; every devhub remote endpoint is HTTPS |
| HTTP server | none (not needed) | `gui_server.spl` already serves HTTP over `std.io.tcp` (SOSIX TCP) |
| WebSocket | none (not needed) | no devhub caller |

devhub's HTTP client therefore still calls `rt_http_request*` directly, through `io.http_client_core`.
That path is unchanged by this record, but it is outside SOSIX.
To route it through SOSIX, SOSIX needs a TLS-capable HTTP client owner, for example `sosix_http_request` with a
TLS session layered over `sosix_tcp_*`, plus a timeout and download variant.
Once that owner exists, `http_client_core` (or devhub's adapters) should move onto it.
No extern was invented to fill this gap.
