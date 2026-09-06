# SSHD RFC 4254 Unsupported Channel-Open Failure v1

The filesystem-launched SSHD accepts only RFC 4254 `session` channels. A
well-formed request for any other channel type now receives
`SSH_MSG_CHANNEL_OPEN_FAILURE` with reason
`SSH_OPEN_UNKNOWN_CHANNEL_TYPE`; it is no longer silently dropped.

The classifier accepts at most a 64 KiB packet, retains no peer-controlled
text, and compares only the exact seven-byte supported type. Long unsupported
type fields are skipped by a validated offset rather than scanned or copied.
It preserves only the fixed numeric fields needed
by the session owner. An exact `session` packet has no trailing
channel-specific fields. A structurally valid session request with a zero peer
maximum-packet value is rejected at channel scope with a resource-shortage
failure; it is not mislabeled as packet corruption. Malformed packets close the
transport before channel-table mutation. A pure rejection mapper used by the
live handler makes recipient and reason-code selection directly spec-coverable.

This change does not create forwarding, process, socket, or exec ownership.
`direct-tcpip`, `forwarded-tcpip`, and vendor channel types remain unsupported
and receive the protocol-required negative response.
