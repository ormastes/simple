# Host Service authentication frame V6

Source:
`test/01_unit/lib/common/contracts/orchestration/host_service_auth_frame_v6_spec.spl`.
Status: **source-only NOT_RUN**. These eight authored pure scenarios establish no
runtime/native/parser/type/build, OS entropy, ready-reader or transport result.
This new leaf belongs to the same initial Controller routing authoring batch 1.
The preceding five-file pure protocol freeze remains immutable.

`HostServiceAuthFrameV6` has seven text fields: `role`, `service_incarnation`,
`client_nonce`, `server_nonce`, `command_digest`, `payload` and `tag`.
The canonical SDN object has exactly nine fields: integer `version: 6`, kind
`host-service-auth-frame`, `role`, `serviceIncarnation`, `clientNonce`,
`serverNonce`, `commandDigest`, `payload` and `tag`, followed by exactly one LF.
Unknown, duplicate, missing, mistyped and noncanonical representations fail.

Public functions are `host_service_auth_frame_validate_v6`,
`host_service_auth_frame_encode_v6`, `host_service_auth_frame_decode_v6`,
`host_service_auth_frame_line_encode_v6` and
`host_service_auth_frame_line_decode_v6` in the new common contract module
`host_service_auth_frame_v6.spl`.

| Role | Required body/context | Inclusive canonical decoded-frame cap |
| --- | --- | --- |
| hello | Empty server nonce, payload and tag; incarnation/client nonce/command digest retain their fixed hex widths. | 4096 bytes |
| challenge | Full context, 64-hex tag, empty payload. | 4096 bytes |
| request | Full context/tag; shared transcript helper requires an exact canonical V6 operation with the same incarnation and outer command digest. | 2097152 bytes |
| reply | Full context/tag; nonempty exact body. | 1048576 bytes |

Caps include canonical field syntax, escape expansion and final LF, not merely
raw inner body size. Exact `sdn_encoded_text_size_v1` preflight occurs before the
escaped frame string is allocated. Shared operation/transcript validation is
reused; this module imports no HMAC, key, tag comparison or entropy primitive.
A correctly shaped tag passes schema checks even when its MAC is wrong; callers
must use the shared authentication helper through the actual retained owner.

Line encoding is the literal prefix `host-service-auth-v6 `, canonical unpadded
base64url of the complete canonical frame, then one LF. Its encoded length is
bounded before base64 allocation/decoding. Generic line decoding first uses the
largest request cap; strict frame decoding then enforces the actual role cap.
The existing strict base64url decoder is wrapped with ASCII and canonical
re-encoding checks, rejecting whitespace, CRLF, padding, alternate alphabets,
nonzero unused tail bits and lossy invalid-UTF-8 aliases. Outgoing challenge/reply
length framing remains the existing caller's transport responsibility; no EOF
or native stream protocol is introduced by this codec.

| Authored scenario | Assertions |
| --- | --- |
| All roles | Canonical nine-field and exact prefix/base64url/LF round trips. |
| Phase fields | Hello/challenge constraints and nonempty reply requirement. |
| Strict SDN | Unknown/duplicate/missing/mistyped fields and noncanonical trailing bytes fail. |
| Request association | Shared canonical operation, outer digest and incarnation checks reject substitutions. |
| Inclusive bounds | Near-limit reply fits; escaped body overflow, globally oversized source and oversized handshake fail. |
| Strict lines | Prefix/alphabet/padding/CRLF/extra line/UTF-8 junk and oversized encoded input are refused. |
| Base64 aliases | Nonzero unused tail bits and invalid UTF-8 replacement cannot alias authenticated text. |
| Exact bytes vs authority | Unicode reply bytes survive; actual shared MAC verification accepts the fixture tag and rejects a schema-valid forged tag. |

Key custody, OS nonce generation, authenticated ready admission, exchange role
gates, one-use state and final Host action authority remain native owner/service
requirements. No pure frame or metadata boolean supplies those capabilities.
