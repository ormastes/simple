# Host Service operation reply V6

Source:
`test/01_unit/lib/common/contracts/orchestration/host_service_operation_reply_v6_spec.spl`.
Status: **source-only NOT_RUN**. No runtime, parser/type/build/native transport,
service execution, cleanup or timing evidence was produced. This leaf is part
of bounded R2 source cycle **2/6**. All original R1 freezes are unchanged.

`HostServiceOperationReplyV6` contains action, service incarnation, operation ID,
scope digest, request digest, pending boolean, exit code integer, payload and
error text. The exact eleven-field canonical SDN record has `version: 6`, kind
`host-operation-reply`, `action`, `serviceIncarnation`, `operationId`,
`scopeDigest`, `requestDigest`, `pending`, `exitCode`, `payload` and `error`,
followed by one LF. Unknown/duplicate/missing/mistyped/noncanonical fields fail.

Public functions in the new common module `host_service_operation_reply_v6.spl`:
`host_service_operation_reply_validate_v6`, `host_service_operation_reply_encode_v6`,
`host_service_operation_reply_decode_v6` and
`host_service_operation_reply_match_v6(reply, request)`.
Match validates both values and returns true only for exact action, incarnation,
operation ID, scope digest and request digest equality; mismatch is an error.
Status operation/scope/request fields are empty exactly as in the status request.
Its opaque payload must separately pass the actual typed Host-status consumer.

Pending is allowed only for execute/inspect/progress/cancel. Status, validate
and prepare cannot report pending operation metadata. Service-stop also requires pending
false, empty operation ID/request digest and the exact requested scope/incarnation.
Its payload may report Host obligations but cannot certify later socket,
listener or credential cleanup. `pending=false` never
means success or proves native cleanup. Existing errors and nonzero exit codes
remain unchanged when pending clears. Nonempty error requires a nonzero outer
exit code; that code is bounded to 0–255. A nonzero exit with empty error is
permitted and is not normalized. Inner process status belongs to the opaque
payload and is not coerced into this outer command range.

The complete canonical reply is at most 1048576 UTF-8 bytes including payload,
error, escapes, metadata and final LF. Exact encoded-size preflight uses the
existing canonical string-size helper before allocating the escaped envelope.
Authentication frames apply an additional independent inclusive limit, so a
reply that fits this codec may still exceed the outer frame after escaping.
No tag, nonce, key, native owner or authority state is created by this module.

| Authored pure scenario | Assertions |
| --- | --- |
| All actions | Exact eleven-field canonical round trips and request identity matching. |
| Pending actions | Execute/inspect/progress/cancel allow pending; status/validate/prepare reject it. |
| Failure preservation | Clearing pending preserves error and nonzero status; identity match does not promote failure to success. |
| Exit constraints | Nonempty error with zero exit and values outside 0–255 fail; 255 is representable. |
| Strict wire | Unknown/duplicate/missing/coerced boolean/integer fields and noncanonical trailing bytes fail. |
| Identity correlation | Action/incarnation/operation/scope/request digest substitutions and status operation metadata fail. |
| Reply bounds/bytes | Near-limit reply fits; escape-expanded payload or error exceeds the inclusive cap; Unicode payload is preserved; oversized source fails. |
| Outer frame bound | A valid inner reply can still fail the independent authentication frame cap. |
| Stop reply failures | Exact stop identity matches while nonpending late Host-close error/nonzero status remain intact; no native cleanup is simulated. |
| Stop reply refusal | Pending, scope/incarnation substitution, operation/request-digest fields and legacy `stop` alias fail. |

These are pure metadata assertions, without fabricated live cleanup ownership.
Authentication, actual typed Host payload checks, operation admission and
retained native owner completion remain separate production gates.
The actual server must quiesce before Host close and retain its auth reader
through MAC reply drain; this pure R2 does not implement or certify those effects.
