# HttpRequestParser: missing Host/field-name strictness (request validation hardening)

Date: 2026-09-16
Status: OPEN

## Observed

`http_server/async_parser_limits_spec.spl` — 7 examples fail. The parser
(src/lib/nogc_async_mut/http_server/parser.spl) enforces line/count/body
limits and Content-Length/chunked framing, but does NOT implement:

- rejection of whitespace between field name and colon (`Host : x` accepted)
- rejection of non-token field names (`X@Trace: v` accepted)
- "400 Missing Host" before request dispatch (no Host/authority requirement)
- rejection of duplicate and malformed Host authorities
- absolute-form target vs Host agreement
- rejection of forbidden control bytes in field values

## Impact

HTTP/1.1 request-smuggling and authority-confusion class defenses pinned by
the spec do not exist in the implementation.

## Expectation

Parser rejects each malformed shape with a 400-prefixed error_message before
dispatch, per the spec's examples.

## Unblock condition

Implement strict field-name/token, Host-presence/uniqueness/format, and
field-value control-byte validation in `parser.spl` (or in a pre-dispatch
validation pass). Re-run the spec. Deliberately left RED per the testing rule
(a correct spec that fails is legitimate).
