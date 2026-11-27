# Pure Host Service operation and authentication V6

This R2 leaf is part of Controller routing source cycle **2/6**. It does not reset
any stopped feature's source-cycle budget. Runtime, native builds, OS producers,
native timing and transport execution are **NOT_RUN**. The prior nine-file
Controller storage freeze is unchanged.

The coherent pure production scope comprises `host_service_operation_v6.spl`,
`host_service_auth_v6.spl`, `host_service_auth_frame_v6.spl` and
`host_service_operation_reply_v6.spl`. R2 changes only operation/reply logic.
There are no native
exports, filesystem/keystore operations, ready-reader ownership, listeners,
challenge producers or transport effects here. OS entropy and authenticated ready
reader/key retention belong to the later actual owner. Metadata never supplies
that authority.

`HostServiceOperationRequestV6` contains action, service incarnation, operation
ID, scope digest, inner request digest and payload text. Canonical encoding has
exactly eight fields: integer version 6, kind `host-operation-request`, `action`,
`serviceIncarnation`, `operationId`, `scopeDigest`, `requestDigest` and `payload`.
The canonical serializer's final newline is part of the exact wire bytes.

Actions are `status`, `validate`, `prepare`, `execute`, `inspect`, `progress`,
`cancel` and `service-stop`. Status has empty operation/scope/request/payload.
Service-stop represents the required current incarnation and 64-hex retained
Host scope fence, with empty operation ID, request digest and payload. The pure
codec validates their shape; the actual owner checks current identity. All other actions require
a valid operation identifier and 64-lowercase-hex scope/request digests.
Validate/prepare/execute require nonempty payload and inner digest
`sha256(operation_id + "\n" + payload)`. Inspect/progress/cancel carry no payload
and retain the original execute digest; the actual retained service must establish
that historical association. A 32-lowercase-hex service incarnation is required
for every action, but its shape does not prove origin or freshness.

The entire encoded operation is bounded to 2097152 UTF-8 bytes, including escaped
payload expansion, field/key syntax and final newline. Before constructing the
encoded/escaped envelope, the validator sums exact canonical punctuation and
`sdn_encoded_text_size_v1` for all string values. Raw input bounds keep arithmetic
bounded. Decoding uses the strict SDN parser, exact field count/names and types,
then canonical re-encoding equality. Unknown/duplicate fields and aliases fail.

`host_service_operation_command_digest_v6` hashes the exact canonical operation
including the final newline. This outer digest covers action/scope/incarnation
and is distinct in meaning from the inner operation/payload digest. Authentication
must never substitute the inner digest for this outer command digest.

`HostServiceAuthContextV6` contains `service_incarnation`, `client_nonce`,
`server_nonce` and `command_digest`. Both nonces and the digest have exact
64-lowercase-hex text shape. Producers must later supply actual OS-generated,
fresh nonce values. A pure shape check explicitly does not prove entropy.

The MAC transcript is exactly the prefix `SIMPLE-HOST-SERVICE-AUTH-V6`, newline,
one canonical seven-field SDN object, then newline. Its fields are `role`,
`serviceIncarnation`, `clientNonce`, `serverNonce`, `commandDigest`, `payloadDigest`
and integer `payloadBytes`. Digest/count refer to the exact UTF-8 body bytes; the
body is not embedded or escaped again into the transcript. Roles are `challenge`,
`request` and `reply`. Challenge body is empty. A request body must be a canonical
V6 operation from the same incarnation and its SHA256 must equal `commandDigest`.
A reply body is at most 1048576 bytes, including multibyte UTF-8 characters.

The existing pure `hmac_sha256(key: text, data: text)` consumes the exact key text:
64 lowercase ASCII hex characters, without implicit hex-to-binary decoding.
That explicit encoding is shared by the later native reader and actual service.
Key shape does not prove entropy, key custody or authenticated enrollment.
Key arguments belong to retained server/library owner scope and are not new
command metadata or a keystore contract.

There is one shared private tag comparison in the auth leaf: exact 64-hex shape,
all 64 positions XOR/OR accumulated, then the existing explicit `black_box`
barrier before equality. Malformed public encoding returns an error; a valid
shape with a wrong MAC returns false. Source structure alone establishes no
native constant-time or side-channel qualification.

The future NativeReadyReader retains its key and permits tag only for role
`request`, verify only for `challenge`/`reply`. Generic pure helpers support all
roles so the actual server can use them too; they do not enforce native custody.
The separately frozen R1 frame codec supplies the canonical nine-field exchange
frames and strict line envelope. This R2 changes neither auth nor frame logic;
their existing operation-validation dependency accepts the additive stop action.

## Service stop boundary

The accepted mode schema is `host-service-auth-v6-mode-schema-20261115.sdn`.
The action is exactly `service-stop`, never a legacy `stop` or bearer conversion.
The pure request/reply codecs only represent and correlate the exact service
incarnation/scope tuple. Stop replies cannot be pending, and late Host-close
failures retain nonzero exit/error metadata. The shared request MAC and outer
command digest bind stop to its exact canonical bytes through the existing
authentication/frame helpers. No shutdown or cleanup effect occurs here.

The actual server must take the canonical auth connection once, verify the
exact current tuple, require the only live connection and apply existing Host
and pane stop guards. It must atomically quiesce before the first actual Host
close and stop accepting/dispatching other work. It retains the auth reader
through MAC reply signing and drain, then closes the socket/listener, reader
and publication owners. A close failure is sticky cleanup-only state with the
first error and actual cleanup carriers retained; it never returns to ready.
A stop reply concerns Host obligations only and does not certify later socket,
listener or credential cleanup. Disconnect never means shutdown or cancellation.
Those ordering/ownership gates are separate actual-server work and NOT_RUN.

R2 is preserved in a new directory; all R1 pure5/frame3/reply3 freezes remain
unchanged. The coherent R2 bundle carries all dependencies, with only operation
and reply production plus their focused specs/manuals and this design changed.

All processing is bounded by the operation/reply limits and fixed metadata
widths. Payload hashing, preflight sizing and canonical checks are linear input
passes; MAC input itself is small fixed metadata. No IO, full-tree scans, retry
loops, implicit environment reads or caches are introduced. Startup/latency/RSS
and native timing remain unqualified rather than inferred from these bounds.
