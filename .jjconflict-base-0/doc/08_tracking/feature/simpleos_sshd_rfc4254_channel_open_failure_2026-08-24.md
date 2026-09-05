# SimpleOS SSHD RFC 4254 channel-open failure

Status: implemented, statically specified, manually unverified by user request.

The live filesystem-launched session path now distinguishes malformed,
supported `session`, and well-formed unsupported channel-open requests. The
last category receives the RFC 4254 unknown-channel-type failure response.

Runtime, build, test, SPipe, benchmark, and optimizer evidence was intentionally
not collected. TCP forwarding remains a separate capability requiring bounded
socket and policy ownership.
