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

## Revision 2026-10-27: corrected contract and bounded caller fix

The original XOR premise above is incorrect. RFC 9113 §8.3.1 permits a
request containing both `:authority` and `host` when they identify the same
entity; a mismatch SHOULD be rejected after normalization. An authority may
also be absent in some request forms, while CONNECT has separate requirements.
See [RFC 9113 §§8.3.1, 8.5](https://www.rfc-editor.org/rfc/rfc9113.html#section-8.3.1)
and [RFC 9110 §4.2.3](https://www.rfc-editor.org/rfc/rfc9110.html#section-4.2.3)
for authority handling and normalization.

The earlier observations that validation admits matching and conflicting
authority/Host pairs, and admits some requests without either source, remain
accurate observations. The assertions that matching pairs and every
no-authority request must be rejected are withdrawn. In the authorized partial
scope, `_decode_and_buffer_request` now drops incoming regular `Host` fields
when a nonempty validated `:authority` exists, then appends one `Host` carrying
that authority. Without `:authority`, it retains regular headers unchanged.
This gives downstream first-match Host lookup one authoritative value.

The partial fix does **not** compare normalized authority and Host values,
reject mismatches, require authority for ordinary requests, or change CONNECT
validation. Those full validation rules remain open. The bug remains **OPEN**;
the caller canonicalization is not closure evidence. The actual-caller HPACK
regression covers matching, conflicting and repeated Host fields, authority
only, Host only, neither, OPTIONS `*`, and CONNECT controls.
