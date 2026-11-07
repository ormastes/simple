# Local gateway frame specification

Executable: `test/01_unit/lib/daemon_sdk/local_gateway_frame_v1_spec.spl`.
Status: **NOT_RUN**; nine authored cases, no runtime or full-gateway PASS.

| Case | Required result |
|---|---|
| Request metadata roundtrip | Exact request ID/action/count; response-domain rejection |
| Response metadata roundtrip | Exact exit code and opaque metadata, no live descriptor |
| Strict field set | Reject caller peer UID, duplicate/missing/wrong typed fields |
| Canonical bounds | Reject padding, trailing data and header above 8192 bytes |
| Prefix arithmetic | Reject high count bytes and request payload above 2 MiB |
| Fragmented payload | Preserve Unicode and embedded NUL across single-byte feeds |
| Count disagreement | Reject prefix/header mismatch before body admission |
| Invalid or incomplete body | Reject malformed UTF-8 and actual premature EOF |
| Empty body | Complete only after exact canonical header |

Native listener, authenticated distinct-UID deployment, owner-before-publication,
SCM one-use handoff, application grants and Host resource settlement require
their own executable evidence. This pure frame suite establishes none of those
claims. Use an admitted pure-Simple producer when root allocates verification;
do not substitute the Rust bootstrap seed or repeat prior green native cases.
