# Host Service operation/authentication V6 pure specification

Executable source:
`test/01_unit/lib/common/contracts/orchestration/host_service_auth_protocol_v6_spec.spl`.
Status: **source-only NOT_RUN**. No parser/type/runtime/build/native execution,
entropy producer, ready reader, service request or timing measurement was run.
R2 source cycle **2/6** adds only the accepted `service-stop` action to the
operation/reply boundary, preserving all R1 freezes in their original directory.

| Authored scenario | Assertions |
| --- | --- |
| Seven actions | Exact status emptiness, nonempty effect payloads, canonical eight-field round trips and retained original execute digests for query actions. |
| Strict wire | Unknown/duplicate/missing/mistyped fields and noncanonical trailing bytes are rejected. |
| Constructed values | Unsupported action, malformed incarnation/operation/scope, changed inner digest and forbidden status/query payloads are refused. |
| Encoded bound | A near-limit plain payload fits; escape expansion exceeds the whole-envelope limit and fails; Unicode/newline/backslash/quote values round trip; oversized source is refused. |
| Outer vs inner digest | Outer digest hashes exact canonical bytes and changes with action/scope while the inner payload digest retains its separate meaning. |
| Golden transcript | An independently spelled canonical challenge transcript fixes domain prefix, field order and values; the tag equals existing pure HMAC on those exact bytes. |
| Roles and bodies | Challenge/request/reply tags verify only their own role/body; role substitution and body tampering fail. |
| Context replay | Changing either nonce, incarnation, command digest or key invalidates a correctly shaped tag. |
| Canonical request body | Same command hash does not admit a different incarnation or noncanonical request envelope. |
| Shape vs provenance | Bad key/nonce/tag/role encodings fail; a deterministic zero-valued fixture can satisfy shape without being claimed as real entropy. |
| Fixed comparison | A changed valid nibble at the first or last MAC position is detected by the shared comparison; this is not a native timing result. |
| UTF-8 reply bound | Exactly one MiB of multibyte body bytes fits and the next scalar is rejected before hashing. |
| Authenticated stop representation | Exact incarnation/scope with empty operation/digest/payload round trips through the existing request MAC/frame helpers; reply/challenge role reuse and changed-scope tag reuse fail. No shutdown is performed. |
| Stop refusal | Operation ID, inner digest, payload, missing scope, wrong incarnation, legacy `stop` and operation-cancel reinterpretation fail. |

Production operation API: `HostServiceOperationRequestV6` and
`host_service_operation_validate_v6`, `host_service_operation_encode_v6`,
`host_service_operation_decode_v6`, `host_service_operation_request_digest_v6`
and `host_service_operation_command_digest_v6`.

Production authentication API: `HostServiceAuthContextV6` and
`host_service_auth_context_validate_v6`, `host_service_auth_transcript_v6`,
`host_service_auth_tag_v6` and `host_service_auth_verify_v6`.
The exact transcript/key encoding and bounds are documented in
`doc/05_design/host_service_auth_protocol_v6.md`.

These pure APIs have no OS/journal/credential authority. Actual entropy, key
custody, ready-record admission, nonce lifecycle, exchange framing, historical
operation association and service request limits remain later owner gates.
The storage freeze and held SSH/composition sources are not changed here.
The R2 coherent bundle reuses byte-identical R1 auth/frame production logic.
Actual stop quiescence, Host close, authenticated reply drain and late cleanup
ownership remain the server owner's separate ordering gates and NOT_RUN.
