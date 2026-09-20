# h2_validate_request_headers: no authority-source ambiguity check

Date: 2026-09-16
Status: OPEN

## Observed

`http_server/h2_hpack_connection_state_spec.spl`
"requires one unambiguous request authority source" fails:
`h2_validate_request_headers` (src/lib/nogc_async_mut/http_server/h2_request_headers.spl)
validates pseudo-header duplication/emptiness but never requires an authority
for non-CONNECT requests, never treats a regular `host` header as an authority
source, and never rejects `:authority` + `host` both present. As a result:

- headers with no authority at all: `valid=true` (spec expects false)
- `:authority` plus `host`: `valid=true` (spec expects false)

## Impact

HTTP/2 request-smuggling class gap: requests without an unambiguous authority
are admitted into dispatch.

## Expectation

RFC 9113 §8.3.1: a request needs exactly one authority — either `:authority`
or a single `host` header; neither-zero nor both is invalid; CONNECT requires
`:authority`.

## Unblock condition

Add the authority-source check to `h2_validate_request_headers` (track
`saw_host` for regular `host` headers; final gate: `saw_authority or saw_host`
exactly one). Re-run the spec.
