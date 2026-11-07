# Runtime binding request and exact target validation

Status: **AUTHORED_UNRUN**. Source-import pure regressions; no socket, native process, container attachment, or readiness evidence.

Source: `test/01_unit/os/apps/smux/runtime_binding_request_v3_spec.spl`.

1. Encode the exact request and retain unsigned revision and child fences. Round-trip values above signed i64, and compare the shared request digest with SHA256 of the canonical wire bytes.
2. Reject padding whitespace extra source and oversized decoded requests. The text protocol accepts only bounded canonical base64url of canonical SDN.
3. Reject extra authority fields and invalid immutable request identities. No request may select a root, command, grant, aliased helper operation, or zero epoch/revision.
4. Expose only the exact current target with attachable incarnation capacity. Closing, absent, exhausted, or cleanup-retained targets cannot be advertised vacant.

Target replies accept exact canonical SDN or one terminal LF added by the
compiled CLI printer; two LFs or other trailing bytes fail. Immutable wire
requests remain exact canonical SDN without this reply-only allowance.

Service incarnation is exactly 32 lowercase hex characters. Parent budget digest is exactly 64 lowercase hex characters and is a retained reference, not a grant. Request UID reuse and durable replay are responsibilities of the configured owner.
