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

## 2026-10-16: narrow lexical repair prepared, qualification pending

Current source confirmed that `parse_header_line` trimmed the raw field name
before validating it, admitting `Host : example.test` and `X@Trace: value`.
It also trimmed raw field values without rejecting control bytes. The feed
caller replaced every lexical failure with `400 Malformed header line`, so
the existing name/value-specific diagnostic assertions could not pass.

The narrow repair validates the untrimmed name as ASCII HTTP tchar bytes and
rejects C0 value bytes except HTAB plus DEL before trimming. Both walks use
the canonical `string_bytes` owner to avoid mixing byte lengths with
character indexes. Failed fields are not stored; feed preserves the precise
name/value diagnostic and enters its existing terminal Error state.

Eight production-parser scenarios were authored in
`test/01_unit/lib/nogc_async_mut/http_server/async_header_lexical_contract_spec.spl`,
with a companion manual under the mirrored `doc/06_spec/01_unit/` path.
They cover all C0/DEL controls, name punctuation and whitespace, legal tchar
punctuation, HTAB and Unicode values, fragmented input and malformed framing.

**AUTHORED_UNEXECUTED:** no qualified self-hosted full CLI was available in
this validation lane. No Rust seed fallback was used. The existing broader
limits specification remains unchanged. Native/compiler/core qualification
and runtime execution remain pending.

**Status remains OPEN.** Host presence, authority validity and absolute-form
target/Host agreement are separate unresolved requirements of this same
record. Qualified bug-DB tool reconciliation is pending; no DB row or CRC
was changed by this repair.
