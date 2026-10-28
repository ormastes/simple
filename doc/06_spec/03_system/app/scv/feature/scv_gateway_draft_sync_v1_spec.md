# SCV native draft sync v1 system specification

Documentation status: hand-authored from the executable specification; the
SSpec doc generator and runtime were unavailable in this worktree.

Executable source: `test/03_system/app/scv/feature/scv_gateway_draft_sync_v1_spec.spl`.
Requirement: `REQ-SCV-GATEWAY-DRAFT-SYNC-001`.

## Scenario: durable binary PUT, exact retry, and GET over real loopback HTTP

Given a private, pre-provisioned draft store root and a host-mapped
`repo-alpha` / `principal-1` bearer grant, when the native bounded client sends
binary bytes containing NUL and non-UTF8 values to the service over a real
loopback TCP socket, then the server returns a receipt with the exact
repository, principal, request id, digest, byte count and state
`local_durable` only after the store owner accepts its durable receipt.

When the client repeats the exact request id and bytes, then the same durable
receipt is returned. When it requests the known digest over a new socket, then
the response state is `local_readback` and its binary payload matches the
original bytes exactly.

## Negative and unit evidence

The focused unit specs reject non-loopback and unprovisioned service roots,
unknown or principal-bearing wire fields, duplicate credentials, wrong
bearers, wrong repository subjects, denied read/write capabilities,
noncanonical base64, oversized payloads, forged response principals, and
durable receipts whose byte count differs from the submitted bytes. Client
preflight proves invalid endpoint/repository input does not acquire credentials.
CLI output refuses existing files and symlink destinations.

## Qualification limit

The scenario source is authored but was not executed. It proves no TLS
qualification, Git object identity, GitHub acceptance, ref update, CI result,
publication, or settlement. Service startup requires explicit loopback
development mode while native TLS serving remains unavailable.
