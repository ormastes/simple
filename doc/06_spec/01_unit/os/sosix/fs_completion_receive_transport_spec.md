# SOSIX Owned Completion Receive Transport

This executable contract covers the bounded, nonblocking client receive seam
between owned-copy IPC syscall 133 and the authenticated filesystem completion
pump.

## Pending poll

A zero service or reply endpoint is a terminal invalid receive contract. Both
the result validator and live polling entrypoint reject it before EAGAIN can be
reported as pending; live polling performs no syscall for that invalid input.

A single poll of an empty reply endpoint returns `EAGAIN` as
`completion-pending`. It does not publish a completion or notification and does
not retry or block.

## Authenticated publication

The receiver accepts only an exact owned IPC envelope whose kernel-copied
metadata names the expected filesystem service source, the client's expected
reply endpoint, the expected API method, async delivery, zero capabilities,
and an exact bounded payload length. The payload then passes through the
completion pump's operation-generation and request-token checks. A valid reply
is published once; replay is rejected without a second notification.

## Rejection cases

The scenarios reject spoofed service sources, swapped reply endpoints, stale
request tokens, truncated or oversized syscall results, and capability-bearing
metadata before publication.

The maximum boundary is also executable: the owned envelope's payload length
may contain the complete 4144-byte encoded completion (48-byte completion
header plus 4096 data bytes). Together with 32 bytes of owned IPC metadata this
forms one accepted 4176-byte envelope; one byte beyond it is rejected.

Executable source:
`test/01_unit/os/sosix/fs_completion_receive_transport_spec.spl`

Implementation:
`src/os/sosix/fs/completion_receive_transport.spl`
