# Test daemon environment identity

The light test daemon may serve a request only when the caller environment is
byte-for-byte identical to the environment of the client that started it. A
long-lived daemon otherwise gives the worker a stale environment and can turn
an explicitly enabled test gate into a skip.

The client computes a deterministic SHA-256 identity over every environment
name and value. Rows are length framed and sorted before hashing. The starting
client and daemon independently fingerprint the effective worker environment;
environment values and secrets are never written to the request directory.
The daemon publishes the digest in the same atomic lock record as its PID.
Shell bookkeeping (`_`, `SHLVL`) is excluded, and `SIMPLE_EXECUTION_MODE` is
normalized to the launcher's forced `interpret` value. The light daemon is a
Linux only service, so environment names retain POSIX case sensitivity; the OS
snapshot API cannot contain NUL bytes, while embedded newlines are safe under
length framing.

Before using an existing daemon, each client recomputes its identity and
compares it with the published value. A missing identity, snapshot failure, or
mismatch takes the direct worker path, which inherits the current caller's
environment. This covers both transitions: unset to set and set to unset.

Every v2 request also carries the approved digest and daemon PID generation.
The daemon validates both against its startup identity and current lock owner
after claiming the request and immediately before execution. A mismatch returns
a typed reroute response; the client executes that spec directly. This closes
the race where one daemon exits and another claims the shared request directory
between the suite-level check and request handling.

The digest is an eligibility check rather than an artifact identity or an
authorization token. It must never be logged as proof of test admission. The
bug database row stays open until a self-hosted runtime proves the stale-daemon
integration scenario and the latency and RSS comparison passes.

## Verification

The canonical unit test must prove ordering independence, value sensitivity,
unset sensitivity, and framing safety. The integration oracle must keep one
daemon PID and generation alive while changing a caller variable, then prove
that the second spec sees the new value or is explicitly routed directly.
Retain wall time and maximum RSS for identical warm-daemon fixtures before and
after the change.
